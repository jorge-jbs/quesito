{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts, MultiParamTypeClasses, ConstraintKinds, FlexibleInstances #-}

module Quesito
  ( Ques
  , runQues
  , MonadEnv
  , R.ask
  , R.runReaderT
  , MonadExcept
  , throwError
  , catchError
  , Location(..)
  , PPrint(pprint)
  , MonadLocatable
  , locatedAt
  , getLocation
  , MonadLog
  , W.tell
  )
  where

import Control.Monad.Trans (lift)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader as R (Reader, ReaderT, MonadReader, runReader, runReaderT, ask)
import Control.Monad.Writer as W (Writer, MonadWriter, runWriter, tell)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError, catchError)

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

type QuesError = String

type MonadExcept m = MonadError QuesError m

type MonadEnv def m = MonadReader (Env.Env def) m

type MonadLog m = MonadWriter String m

class Monad m => MonadLocatable m where
  getLocation :: m (Maybe Location)
  locatedAt :: m a -> Location -> m a

instance MonadLocatable m => MonadLocatable (ReaderT e m) where
  getLocation =
    lift getLocation

  locatedAt m loc = do
    e <- ask
    let m' = runReaderT m e
    lift $ locatedAt m' loc

instance MonadWriter String Ques where
  tell s = Ques $ lift $ lift $ tell [s]

instance MonadLocatable Ques where
  getLocation =
    location <$> get

  locatedAt m loc = do
    oldLoc <- getLocation
    modify (\st -> st { location = Just loc })
    x <- m
    modify (\st -> st { location = oldLoc })
    return x
