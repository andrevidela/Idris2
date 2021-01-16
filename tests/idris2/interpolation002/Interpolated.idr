module Interpolated


data Eq = Add Eq Eq | N = Nat

Show Eq where
  Add a b = s"{a} + {b}"
  N a = show a

main : IO ()
main = printLn $ Add (N 3) (Add (N 2) (N 0))
