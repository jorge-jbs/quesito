module Main where

import Quesito.Eval
import Quesito.Expr
import Quesito.Parse
import Quesito.TypeCheck

main :: IO ()
main = do
  input <- getContents
  let
    expr
      = either (error . show) id
      $ parse input
  case annotate expr of
    Just expr' ->
      case typeCheck expr' of
        Just _ ->
          putStrLn
            $ show
            $ eval expr
        Nothing ->
          putStrLn "Type checking failed"
    Nothing ->
      putStrLn "Annotation failed"
