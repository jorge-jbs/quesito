{-# LANGUAGE
  FlexibleContexts,
  FlexibleInstances,
  StandaloneDeriving,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses
#-}

module Quesito.TT.TypeAnn
  ( TContext
  , Env
  , Options(..)
  , typeInfAnn
  , typeCheckAnn
  , typeInfAnn'
  , typeCheckAnn'
  , TypeAnnM
  , runTypeAnn
  )
  where

import Quesito
import Quesito.Marked
import Quesito.Marked.Mark
import Quesito.TT (AttrLit(..), deBruijnize)
import Quesito.Ann.Eval hiding (TContext, Env)
import qualified Quesito.Ann as Ann
import qualified Quesito.Env as Env
import qualified Quesito.Ann.Unify as Unify

import Data.List (find)
import Control.Monad (unless)
import Control.Monad.Trans (lift)
import Control.Monad.Reader (MonadReader)
import Control.Monad.Writer as W (MonadWriter, WriterT, runWriterT, tell, mapWriterT)
import Control.Monad.Error (MonadError)
import Data.Default

type TContext =
  [ ( String -- ^ var
    , Value  -- ^ type
    , Ann.Term  -- ^ annotated type
    )
  ]

type Env = Env.Env Ann.Def

data Options
  = Options
      { inferVars :: Bool
      }

instance Default Options where
  def =
    Options
      { inferVars = False
      }

newtype TypeAnnM m a = TypeAnnM
  { unTypeAnnM :: W.WriterT [Unify.Entry Ann.Term] m a
  }

deriving instance Functor m => Functor (TypeAnnM m)
deriving instance Applicative m => Applicative (TypeAnnM m)
deriving instance Monad m => Monad (TypeAnnM m)

instance Monad m => MonadGenProblems Ann.Term (TypeAnnM m) where
  addMetaVar x ty = TypeAnnM $ tell [Unify.MV x ty Unify.Hole]
  addProblem p = TypeAnnM $ tell [Unify.Prob Unify.Active p]

instance W.MonadWriter String m => W.MonadWriter String (TypeAnnM m) where
  tell = TypeAnnM . lift . tell

instance MonadError QuesError m => MonadError QuesError (TypeAnnM m) where
  throwError = TypeAnnM . lift . throwError

instance MonadLocatable m => MonadLocatable (TypeAnnM m) where
  askLoc = TypeAnnM $ lift askLoc
  withLoc = flip (mapTypeAnn . flip withLoc)
    where
      mapTypeAnn
        :: (m (w, [Unify.Entry Ann.Term]) -> n (w', [Unify.Entry Ann.Term]))
        -> TypeAnnM m w -> TypeAnnM n w'
      mapTypeAnn f = TypeAnnM . mapWriterT f . unTypeAnnM

runTypeAnn :: TypeAnnM m a -> m (a, [Unify.Entry Ann.Term])
runTypeAnn = W.runWriterT . unTypeAnnM

typeInfAnn
  :: ( MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m
     , MonadGenProblems Ann.Term m
     )
  => TContext
  -> Term
  -> m
       ( Value
       , Ann.Term  -- ^ annotated input term
       )
typeInfAnn = typeInfAnn' def

typeInfAnn'
  :: ( MonadEnv Ann.Def m, MonadLog m, MonadExcept m, MonadLocatable m
     , MonadGenProblems Ann.Term m
     )
  => Options
  -> TContext
  -> Term
  -> m
       ( Value
       , Ann.Term  -- ^ annotated input term
       )
typeInfAnn' opts ctx (Local x u) = do
  tell ("typeInfAnn' Local: " ++ show (Local x u))
  case find (\(x', _, _) -> x == x') ctx of
    --Just (_, ty@(VType _ (VAttrLit v)), annTy) ->
    Just (_, ty, annTy) -> do
      (tyTy, _) <- typeInfAnn' opts ctx $ Ann.downgrade annTy
      case tyTy of
        VType _ (VAttrLit v) ->
          if u >= v then
            return (ty, Ann.Local x annTy u)
          else do
            loc <- askLoc
            throwError
              ("Uniqueness error at " ++ pprint loc ++ ". " ++
               "Variable " ++ x ++ " should be " ++ show v ++
               " and it is " ++ show u)
        _ ->
          throwError "Type of type is not type!"
    --Just (_, ty, annTy) ->
      --return (ty, Ann.Local x annTy u)
    Nothing -> do
      loc <- askLoc
      env <- askEnv
      tell (show $ Env.keys env)
      tell (show $ map (\(v, _, _) -> v) ctx)
      throwError ("Local variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' _ ctx (Meta x) =
  throwError ("Can't infer type of metavariable: " ++ x)
typeInfAnn' _ ctx (Global x) = do
  tell ("typeInfAnn' _ ctx (Global x) = do")
  env <- askEnv
  case Env.lookup x env of
    Just (Ann.TypeDef n annTy _) | x == n -> do
      ty' <- eval [] annTy
      return (ty', Ann.Global x annTy)
    Just (Ann.TypeDef _ _ conss) ->
      case lookup x conss of
        Just annTy -> do
          ty' <- eval [] annTy
          return (ty', Ann.Global x annTy)
        Nothing -> do
          env <- askEnv
          tell ("env: " ++ show (Env.keys env))
          tell ("ctx: " ++ show (map (\(v, _, _) -> v) ctx))
          throwError "Internal error"
    Just (Ann.PatternMatchingDef _ _ annTy _) -> do
      ty' <- eval [] annTy
      return (ty', Ann.Global x annTy)
    Just (Ann.ExternDef _ annTy _) -> do
      ty' <- eval [] annTy
      return (ty', Ann.Global x annTy)
    Nothing -> do
      loc <- askLoc
      env <- askEnv
      tell ("env: " ++ show (Env.keys env))
      tell ("ctx: " ++ show (map (\(v, _, _) -> v) ctx))
      throwError ("Global variable not found at " ++ pprint loc ++ ": " ++ x)
typeInfAnn' opts ctx (BaseType i) = do
  tell ("typeInfAnn' opts ctx (BaseType i) = do")
  return
    ( VType (i+1) $ VAttrLit SharedAttr
    , Ann.BaseType i
    )
typeInfAnn' opts ctx UniquenessAttr = do
  tell ("typeInfAnn' opts ctx UniquenessAttr = do")
  return
    ( VType 0 $ VAttrLit SharedAttr
    , Ann.UniquenessAttr
    )
typeInfAnn' opts ctx (AttrLit u) = do
  tell ("typeInfAnn' opts ctx (AttrLit u) = do")
  return (VUniquenessAttr, Ann.AttrLit u)
typeInfAnn' opts ctx (Type i u) = do
  tell ("typeInfAnn' opts ctx (Type i u) = do")
  (_, annU) <- typeInfAnn' opts ctx u
  u' <- eval [] annU
  return (VType (i + 1) u', Ann.Type i annU)
typeInfAnn' opts ctx (Attr ty u) = do
  tell ("typeInfAnn' Attr: " ++ show (Attr ty u))
  (tyTy, annTy) <- typeInfAnn' opts ctx ty
  let VBaseType i = tyTy
  (_, annU) <- typeInfAnn' opts ctx u
  u' <- eval [] annU
  return (VType i u', Ann.Attr annTy annU)
typeInfAnn' _ _ (BytesType n) = do
  tell ("typeInfAnn' _ _ (BytesType n) =")
  return (VBaseType 0, Ann.BytesType n)
typeInfAnn' _ _ (Num n) = do
  tell ("typeInfAnn' _ _ (Num n) = do")
  return (VBytesType 4, Ann.Num n 4)
  --loc <- askLoc
  --throwError ("Cannot infer byte size of number " ++ show n ++ ": " ++ pprint loc)
typeInfAnn' _ _ (BinOp op) = do
  tell ("typeInfAnn' _ _ (BinOp op) = do")
  ty <- eval []
    (Ann.Attr
      (Ann.Pi
        ""
        (Ann.Attr (Ann.BytesType 4) (Ann.AttrLit SharedAttr))
        (Ann.Attr
          (Ann.Pi
            ""
            (Ann.Attr (Ann.BytesType 4) (Ann.AttrLit SharedAttr))
            (Ann.Attr (Ann.BytesType 4) (Ann.AttrLit SharedAttr))
          )
          (Ann.AttrLit SharedAttr)
        )
      )
      (Ann.AttrLit SharedAttr)
    )
  return (ty, Ann.BinOp op)
typeInfAnn' _ _ (UnOp op) = do
  tell ("typeInfAnn' _ _ (UnOp op) = do")
  ty <- eval [] (Ann.Pi "" (Ann.BytesType 4) (Ann.BytesType 4))
  return (ty, Ann.UnOp op)
typeInfAnn' opts ctx (Pi x e f) = do
  tell ("typeInfAnn' opts ctx (Pi x e f) = do")
  (ty, annE) <- typeInfAnn' opts ctx e
  case ty of
    VType i _ -> do
      e' <- eval [] annE
      (t', annF) <- typeInfAnn' opts ((x, e', annE) : ctx) f
      case t' of
        VType j _ ->
          return (VBaseType (max i j), Ann.Pi x annE annF)
        _ -> do
          loc <- askLoc
          throwError ("1: " ++ pprint loc)
    _ -> do
      loc <- askLoc
      throwError ("2: " ++ pprint loc)
typeInfAnn' opts ctx (App e f) = do
  tell ("typeInfAnn' App: " ++ show (App e f) ++ " {")
  (s, annE) <- typeInfAnn' opts ctx e
  case s of
    VAttr (VPi v t t' (Closure ctx')) _ -> do
      (annF, _) <- typeCheckAnn' opts ctx f t
      f' <- eval [] annF
      x <- eval ((v, f') : ctx') t'
      tell "}"
      tell (show $ quote x)
      return (x, Ann.App annE annF)
    _ -> do
      loc <- askLoc
      let qs = quote s
      throwError ("Applying to non-function at " ++ pprint loc ++ ": " ++ show qs)
typeInfAnn' opts ctx (Ann e ty) = do
  tell ("typeInfAnn' opts ctx (Ann e ty) = do")
  (tyTy, annTy) <- typeInfAnn' opts ctx ty
  case tyTy of
    VType _ _ -> do
      ty' <- eval [] annTy
      (annE, _) <- typeCheckAnn' opts ctx e ty'
      return (ty', annE)
    _ ->
      throwError ""
typeInfAnn' _ _ e@(Lam _ _) = do
  tell ("typeInfAnn' _ _ e@(Lam _ _) =")
  throwError ("Can't infer type of lambda expression " ++ show e)
typeInfAnn' opts ctx (Loc loc t) = do
  tell ("typeInfAnn' opts Loc: " ++ show t)
  typeInfAnn' opts ctx t `withLoc` loc

typeCheckAnn
  :: ( MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m
     , MonadGenProblems Ann.Term m
     )
  => TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> m
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn = typeCheckAnn' def

typeCheckAnn'
  :: ( MonadLog m, MonadExcept m, MonadEnv Ann.Def m, MonadLocatable m
     , MonadGenProblems Ann.Term m
     )
  => Options
  -> TContext
  -> Term  -- ^ expr
  -> Value  -- ^ type
  -> m
       ( Ann.Term  -- ^ annotated expr
       , Ann.Term  -- ^ annotated type
       )
typeCheckAnn' opts _ (Local v u) ty | inferVars opts = do
  let annTy = quote ty
  return (Ann.Local v annTy u, annTy)
typeCheckAnn' opts _ (Meta v) ty = do
  let annTy = quote ty
  addMetaVar v annTy
  return (Ann.Meta v annTy, annTy)
typeCheckAnn' opts ctx (Lam x e) (VPi x' v w (Closure ctx')) = do
  tell ("typeCheckAnn' opts Lam: " ++ show e)
  w' <- eval ctx' w
  let annV = quote v
  (annE, annW') <- typeCheckAnn' opts ((x, v, annV) : ctx) e w'
  return (Ann.Lam x annV annE, Ann.Pi x' annV annW')
typeCheckAnn' _ _ (Lam _ _) _ = do
  loc <- askLoc
  throwError ("6: " ++ pprint loc)
typeCheckAnn' _ _ (Num x) (VAttr (VBytesType n) _) = do
  if x >= 0 && fromIntegral x < (2^(n*8) :: Integer) then
    return (Ann.Num x n, Ann.BytesType n)
  else do
    loc <- askLoc
    if x < 0 then
      throwError ("Bytes cannot be negative numbers: " ++ pprint loc)
    else
      throwError ("Number " ++ show x ++ " is larger than byte size (" ++ show n ++ "): " ++ pprint loc)
typeCheckAnn' opts ctx t (VType j (VAttrLit v)) = do
  (t', annT) <- typeInfAnn' opts ctx t
  case t' of
    VType i (VAttrLit u) ->
      if i <= j && u == v then
        return (annT, Ann.Type j (Ann.AttrLit v))
      else do
        loc <- askLoc
        throwError ("Incorrect type universe at " ++ pprint loc ++ ". Expected level " ++ show j ++ " and got " ++ show i)

    v -> do
      loc <- askLoc
      let qv = quote v
      throwError ("Expected type at " ++ pprint loc ++ " and got: " ++ show qv)
typeCheckAnn' opts ctx (Loc loc t) ty = do
  tell ("typeCheckAnn' opts Loc: " ++ show t)
  typeCheckAnn' opts ctx t ty `withLoc` loc
typeCheckAnn' opts ctx t ty = do
  tell ("aonde emoh llegao: " ++ show t ++ " ;" ++ show (quote ty))
  tell (show $ map (\(v, _, _) -> v) ctx)
  (ty', annT) <- typeInfAnn' opts ctx t
  let qty = quote ty
      qty' = quote ty'
  case (ty, ty') of
    (VNormal (NMeta _ _), _) -> do
      let tyTy = Ann.typeInf qty
          tyTy' = Ann.typeInf qty'
      addProblem $ Unify.Unify $ Unify.EQN qty tyTy qty' tyTy'
      return (annT, qty')
    (_, VNormal (NMeta _ _)) ->
      return (annT, qty)
    _ -> do
      loc <- askLoc
      unless
        (deBruijnize (unmark $ Ann.downgrade qty) == deBruijnize (unmark $ Ann.downgrade qty'))
        (throwError ("Type mismatch at " ++ pprint loc ++ ". Expected " ++ pprint qty ++ " and got " ++ pprint qty'))
      return (annT, qty)
