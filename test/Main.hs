module Main where
import BDD
import DAG
import System.Exit

main :: IO ()
main = do
  okDag <- dagTestAll
  okBdd <- bddTestAll
  if and [okDag, okBdd]
    then exitSuccess
    else exitFailure
