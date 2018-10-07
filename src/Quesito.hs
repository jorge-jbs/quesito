{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Quesito
  ( Ques
  , Location(..)
  , runQues
  , throwError
  , catchError
  , locatedAt
  , getLocation
  , tell
  )
  where

import Control.Monad.Writer (Writer, MonadWriter, runWriter, tell)
import Control.Monad.State (StateT, MonadState, evalStateT, get, modify)
import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError, catchError)

data Location
  = Location
      Int  -- ^ line
      Int  -- ^ column
  deriving Eq

instance Show Location where
  show (Location y x) =
    "line " ++ show y ++ " and column " ++ show x

data QuesState
  = QuesState
      { location :: Maybe Location
      }

newtype Ques a = Ques { unQues :: (StateT QuesState (ExceptT String (Writer [String])))  a }
  deriving (Functor, Applicative, Monad, MonadError String, MonadState QuesState, MonadWriter [String])

runQues :: Ques a -> (Either String a, String)
runQues =
  mapSnd (concat . map (\x -> "LOG: " ++ x ++ "\n")) . runWriter . runExceptT . flip evalStateT (QuesState Nothing) . unQues
  where
    mapSnd :: (b -> c) -> (a, b) -> (a, c)
    mapSnd f (x, y) = (x, f y)

getLocation :: Ques (Maybe Location)
getLocation =
  location <$> get

locatedAt :: Ques a -> Location -> Ques a
locatedAt m loc = do
  oldLoc <- getLocation
  modify (\st -> st { location = Just loc })
  x <- m
  modify (\st -> st { location = oldLoc })
  return x
