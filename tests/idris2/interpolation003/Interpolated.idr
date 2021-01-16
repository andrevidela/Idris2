module Interpolated

str : String
str = "strings"

main : IO ()
main = printLn $ s"nesting {s"interpolated {str}"} should work"
