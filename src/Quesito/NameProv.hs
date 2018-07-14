module Quesito.NameProv (NameProv, newName, runNameProv) where

import Control.Monad.State.Lazy (State, get, modify, evalState)

newtype NameProv a = NameProv (State Int a)

instance Functor NameProv where
  fmap f (NameProv s) = NameProv (f <$> s)

instance Applicative NameProv where
  pure x = NameProv (pure x)
  NameProv fs <*> NameProv s = NameProv (fs <*> s)

instance Monad NameProv where
  NameProv s >>= f =
    NameProv
      (s >>= \a -> case f a of
          NameProv s' -> s'
      )

newName :: NameProv String
newName = NameProv $ do
  n <- get
  modify (+1)
  return ("x" ++ show n)

runNameProv :: NameProv a -> a
runNameProv (NameProv st) = evalState st 0
