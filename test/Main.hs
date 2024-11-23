module Main where
import DAG

main :: IO ()
main = do
  dagTestAll >>= print
