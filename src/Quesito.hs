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
  , MonadGenHoles(..)
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
import Control.Monad.State (StateT, MonadState, evalStateT, get, gets, modify)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError, catchError)

import Quesito.Ann.UnifyM
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
      , holeName :: Int
      }

newtype Ques a = Ques { unQues :: StateT QuesState (ExceptT String (Writer [String])) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadState QuesState, MonadFix)

runQues :: Ques a -> (Either String a, String)
runQues =
  mapSnd (concat . map (\x -> "; LOG: " ++ x ++ "\n")) . runWriter . runExceptT . flip evalStateT (QuesState Nothing 0) . unQues
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
  addProblem :: Problem t -> m ()

instance MonadGenProblems t m => MonadGenProblems t (ReaderT r m) where
  addProblem = ReaderT . const . addProblem

class Monad m => MonadGenHoles i m where
  genHole :: m i

instance MonadGenHoles Int Ques where
  genHole = do
    i <- gets holeName
    modify (\st -> st { holeName = i + 1 })
    return i

instance MonadGenHoles i m => MonadGenHoles i (ReaderT r m) where
  genHole = ReaderT $ const genHole
