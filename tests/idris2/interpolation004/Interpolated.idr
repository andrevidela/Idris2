module Interpolated

str : String
str = "strings"

main : IO ()
main = printLn $ s"normal values should be shown: {3} but strings should be concatenated: {str}"
