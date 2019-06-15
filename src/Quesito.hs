{-# LANGUAGE
GeneralizedNewtypeDeriving,
FlexibleContexts,
MultiParamTypeClasses,
ConstraintKinds,
FlexibleInstances,
StandaloneDeriving,
GeneralizedNewtypeDeriving
#-}

module Quesito
  ( Ques
  , runQues
  , debugQues
  , QuesError
  , MonadEnv
  , askEnv
  , withEnv
  , MonadExcept
  , throwError
  , catchError
  , MonadGenProblems(..)
  , Location(..)
  , PPrint(pprint)
  , MonadLocatable
  , askLoc
  , withLoc
  , MonadLog(..)
  , W.tell
  )
  where

import Control.Monad.Trans (lift)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader as R (Reader, ReaderT(..), MonadReader, runReader, runReaderT, ask)
import Control.Monad.Writer as W (Writer, MonadWriter, runWriter, tell)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError, catchError)

import Quesito.Ann.Unify
import qualified Quesito.Env as Env

class PPrint a where
  pprint :: a -> String

data Location
  = Location
      Int  -- ^ line
      Int  -- ^ column
  deriving (Eq, Show)

instance PPrint Location where
  pprint (Location y x) =
    "line " ++ show y ++ " and column " ++ show x

instance PPrint a => PPrint (Maybe a) where
  pprint (Just x) =
    pprint x
  pprint Nothing =
    "MISSING"

data QuesState
  = QuesState
      { location :: Maybe Location
      }

newtype Ques a = Ques { unQues :: StateT QuesState (ExceptT String (Writer [String])) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadState QuesState, MonadFix)

runQues :: Ques a -> (Either String a, String)
runQues =
  mapSnd (concat . map (\x -> "; LOG: " ++ x ++ "\n")) . runWriter . runExceptT . flip evalStateT (QuesState Nothing) . unQues
  where
    mapSnd :: (b -> c) -> (a, b) -> (a, c)
    mapSnd f (x, y) = (x, f y)

debugQues :: Ques a -> IO a
debugQues m = do
  let (eith, w) = runQues m
  putStrLn w
  case eith of
    Left err ->
      error err
    Right x ->
      return x

type QuesError = String

type MonadExcept m = MonadError QuesError m

type MonadEnv def m = MonadReader (Env.Env def) m

askEnv :: MonadReader r m => m r
askEnv = R.ask

withEnv :: ReaderT r m a -> r -> m a
withEnv = R.runReaderT

type MonadLog m = MonadWriter String m

class Monad m => MonadLocatable m where
  askLoc :: m (Maybe Location)
  withLoc :: m a -> Location -> m a

instance MonadLocatable m => MonadLocatable (ReaderT e m) where
  askLoc =
    lift askLoc

  withLoc m loc = do
    e <- ask
    let m' = runReaderT m e
    lift $ withLoc m' loc

instance MonadWriter String Ques where
  tell s = Ques $ lift $ lift $ tell [s]

instance MonadLocatable Ques where
  askLoc =
    location <$> get

  withLoc m loc = do
    oldLoc <- askLoc
    modify (\st -> st { location = Just loc })
    x <- m
    modify (\st -> st { location = oldLoc })
    return x

class Monad m => MonadGenProblems t m where
  addMetaVar :: String -> t -> m ()
  addProblem :: Problem t -> m ()

instance MonadGenProblems t m => MonadGenProblems t (ReaderT r m) where
  addMetaVar x y = ReaderT $ (\r -> addMetaVar x y)
  addProblem x = ReaderT $ (\r -> addProblem x)

class Monad m => MonadUnify t m where
  pushL :: Entry t -> m ()
  pushR :: Either (Subs t) (Entry t) -> m ()
  popL :: m (Entry t)
  popR :: m (Either (Subs t) (Entry t))
