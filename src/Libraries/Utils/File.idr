module Libraries.Utils.File

import System.File

export
record FileData where
  constructor MkFileData
  name : String
  content : String

export
(.getName) : FileData -> String
(.getName) = name

export
(.getContent) : FileData -> String
(.getContent) = content

export
readFileData : String -> IO (Either FileError FileData)
readFileData filename = do
  content <- readFile filename
  pure (map (MkFileData filename) content)
