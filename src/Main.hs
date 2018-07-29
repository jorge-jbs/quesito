module Main where

import Control.Monad (unless)

import Quesito.TT
import Quesito.Parse

main :: IO ()
main = do
  input <- getContents
  let
    (Inf (Ann expr ty))
      = either (error . show) id
      $ parse input
  unless (fmap quote (typeInf [] ty) == Right (quote (VType 1))) (error "___")
  case typeCheck [] expr (evalInf [] ty) of
    Right () ->
      putStrLn
        $ show
        $ quote
        $ evalCheck [] expr
    Left err ->
      putStrLn ("Type checking failed: " ++ err)
