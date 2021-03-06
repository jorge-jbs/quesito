{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveTraversable #-}

module Quesito.Env
  ( Definition(..)
  , Env
  , empty, lookup, keys, insert, append, fromList
  )
  where

import Prelude hiding (lookup)

import Data.Default
import Data.List (find)

class Definition def where
  getNames :: def -> [String]

newtype Env a = Env { unEnv :: [a] }
  deriving (Show, Functor, Foldable, Traversable)

empty :: Env a
empty = Env []

instance Default (Env a) where
  def =
    empty

lookup :: Definition a => String -> Env a -> Maybe a
lookup k =
  find (elem k . getNames) . unEnv

keys :: Definition a => Env a -> [String]
keys =
  foldl (++) [] . map getNames . unEnv

insert :: a -> Env a -> Env a
insert d (Env env) =
  Env (env ++ [d])

append :: Env a -> Env a -> Env a
append (Env env1) (Env env2) =
  Env (env1 ++ env2)

fromList :: [a] -> Env a
fromList = Env
