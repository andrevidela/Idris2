module Interpolated

interpolated : String
interpolated = "interpolated"

main : IO ()
main = printLn $ s"escaped characters should work: s\"this is an \{{interpolated}\} string\""
