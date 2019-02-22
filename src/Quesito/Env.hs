module Quesito.Env
  ( Definition(..)
  , Env
  , empty, lookup, keys, insert, append
  )
  where

import Prelude hiding (lookup)

import Data.List (find)

class Definition def where
  getNames :: def -> [String]

newtype Env a = Env { unEnv :: [a] }

empty :: Env a
empty = Env []

lookup :: Definition a => String -> Env a -> Maybe a
lookup k =
  find (elem k . getNames) . unEnv

keys :: Definition a => Env a -> [String]
keys =
  foldl (++) [] . map getNames . unEnv

insert :: a -> Env a -> Env a
insert d (Env env) =
  Env (d : env)

append :: Env a -> Env a -> Env a
append (Env env1) (Env env2) =
  Env (env1 ++ env2)

instance Functor Env where
  fmap f = Env . fmap f . unEnv
