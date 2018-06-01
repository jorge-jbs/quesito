
module Main where

import Parse

main = do
  putStrLn . show $ parse "(+ 1 2)"
