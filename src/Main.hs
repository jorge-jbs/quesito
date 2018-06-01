
module Main where

import Parse
import UntypedLambdaCalculus

main = do
  let Just res = toLambda $ parse "(((lambda x (lambda y y)) 1) 2)"
  putStrLn $ show $ beta $ beta $ res
