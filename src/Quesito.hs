{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Quesito
  ( Ques
  , runQues
  , throwError
  , catchError
  )
  where

import Control.Monad.Except (Except, MonadError, runExcept, throwError, catchError)

newtype Ques a = Ques { unQues :: Except String a }
  deriving (Functor, Applicative, Monad, MonadError String)

runQues :: Ques a -> Either String a
runQues = runExcept . unQues
