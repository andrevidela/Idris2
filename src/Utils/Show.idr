module Utils.Show

||| Show a semiring with a space after the relevant values, no space for `top`
public export
interface ShowRing rig where
  ||| Show function for semirings
  ||| `top` value should always the empty string
  showAppendSpace : rig -> String
  ||| Show function for semirings
  ||| `top` value should always the empty string
  showSurroundSpace : rig -> String
  ||| Show function for semirings in holes
  ||| Nat value is the width
  showInHole : Nat -> rig -> String

