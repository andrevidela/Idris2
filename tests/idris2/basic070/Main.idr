module Main

import Lib

(|:>) : (a -> b) -> a -> b
f |:> x = f x
