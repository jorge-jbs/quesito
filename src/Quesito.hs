{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleContexts #-}

module Quesito
  ( Ques
  , Location(..)
  , PPrint(pprint)
  , runQues
  , MonadQues
  , throwError
  , catchError
  , locatedAt
  , getLocation
  , Quesito.tell
  )
  where

import Control.Monad.Writer as W (Writer, MonadWriter, runWriter, tell)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError, catchError)

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

class (Monad m, MonadError String m) => MonadQues m where
  getLocation :: m (Maybe Location)
  locatedAt :: m a -> Location -> m a
  tell :: String -> m ()

data QuesState
  = QuesState
      { location :: Maybe Location
      }

newtype Ques a = Ques { unQues :: StateT QuesState (ExceptT String (Writer [String])) a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadState QuesState, MonadWriter [String])

instance MonadQues Ques where
  getLocation =
    location <$> get

  locatedAt m loc = do
    oldLoc <- getLocation
    modify (\st -> st { location = Just loc })
    x <- m
    modify (\st -> st { location = oldLoc })
    return x

  tell = W.tell . (:[])

runQues :: Ques a -> (Either String a, String)
runQues =
  mapSnd (concat . map (\x -> "; LOG: " ++ x ++ "\n")) . runWriter . runExceptT . flip evalStateT (QuesState Nothing) . unQues
  where
    mapSnd :: (b -> c) -> (a, b) -> (a, c)
    mapSnd f (x, y) = (x, f y)
