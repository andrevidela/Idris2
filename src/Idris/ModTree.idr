module Idris.ModTree

import Core.Binary
import Core.Directory
import Core.Metadata
import Core.InitPrimitives
import Core.UnifyState

import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL.Common
import Idris.Syntax
import Idris.Pretty

import Data.Either
import Data.String

import System.Directory
import System.Clock

import Libraries.Data.StringMap
import Libraries.System.Tasker

%default covering

record ModTree where
  constructor MkModTree
  nspace : ModuleIdent
  sourceFile : Maybe String
  deps : List ModTree

covering
Show ModTree where
  show t = show (sourceFile t) ++ " " ++ show (nspace t) ++ "<-" ++ show (deps t)

data TimeRef : Type where

Time : Type
Time = Ref TimeRef (SortedMap String (Clock Duration))

withTiming : Time => String -> Core a -> Core a
withTiming fnName f = do
  start <- coreLift $ clockTime Monotonic
  result <- f
  end <- coreLift $ clockTime Monotonic
  let delta = timeDifference end start
  update TimeRef (update (Just . maybe delta (addDuration delta)) fnName)
  pure result

-- A module file to build, and its list of dependencies
-- From this we can work out if the source file needs rebuilding, assuming
-- things are build in dependency order. A source file needs rebuilding
-- if:
--  + Its corresponding ttc is older than the source file
--  + Any of the import ttcs are *newer* than the corresponding ttc
--    (If so: also any imported ttc's fingerprint is different from the one
--    stored in the source file's ttc)
public export
record BuildMod where
  constructor MkBuildMod
  buildFile : String
  buildNS : ModuleIdent
  imports : List ModuleIdent

export
Show BuildMod where
  show t = buildFile t ++ " [" ++ showSep ", " (map show (imports t)) ++ "]"

data AllMods : Type where

mkModTree : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            {auto a : Ref AllMods (List (ModuleIdent, ModTree))} ->
            FC ->
            (done : List ModuleIdent) -> -- if 'mod' is here we have a cycle
            (modFP : Maybe FileName) -> -- Sometimes we know already know what the file name is
            (mod : ModuleIdent) ->      -- Otherwise we'll compute it from the module name
            Core ModTree
mkModTree loc done modFP mod
  = if mod `elem` done
       then throw (CyclicImports (done ++ [mod]))
       else
          -- Read imports from source file. If the source file isn't
          -- available, it's not our responsibility
          catch (do all <- get AllMods
                    -- If we've seen it before, reuse what we found
                    case lookup mod all of
                         Nothing =>
                           do file <- maybe (nsToSource loc mod) pure modFP
                              setCurrentElabSource file -- for error printing purposes
                              modInfo <- readHeader file mod
                              let imps = map path (imports modInfo)
                              if mod `elem` imps
                                then coreFail $ CyclicImports [mod, mod]
                                else do
                                  ms <- traverse (mkModTree loc (mod :: done) Nothing) imps
                                  let mt = MkModTree mod (Just file) ms
                                  update AllMods ((mod, mt) ::)
                                  pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err =>
                    case err of
                         CyclicImports {} => throw err
                         ParseFail {} => throw err
                         LexFail {} => throw err
                         LitFail {} => throw err
                         _ => pure (MkModTree mod Nothing []))

data DoneMod : Type where
data BuildOrder : Type where

modTreeToDAG : ModTree -> DAG ModuleIdent BuildMod
modTreeToDAG modTree =
    MkDAG' (moduleItems modTree empty)
           (moduleTree modTree empty)
  where
    -- we don't keep track of dependencies in the map of items
    moduleItems : ModTree -> SortedMap ModuleIdent BuildMod -> SortedMap ModuleIdent BuildMod
    moduleItems (MkModTree nspace Nothing deps) acc
      = -- trace "module \{show nspace} does not have a file associated" $
        foldr moduleItems acc deps
    moduleItems (MkModTree nspace (Just filename) deps) acc
      = let dependencies = map (.nspace) deps
        in foldr moduleItems
          (insert nspace
              (MkBuildMod filename nspace dependencies)
              acc)
          deps

    moduleTree : ModTree ->
      SortedMap ModuleIdent (SortedSet ModuleIdent) ->
      SortedMap ModuleIdent (SortedSet ModuleIdent)
    moduleTree (MkModTree _      Nothing  _   ) acc = acc
    moduleTree (MkModTree nspace (Just _) deps) acc
      = let realDeps = filter (isJust . sourceFile) deps
            dependencies = map (.nspace) realDeps
            newAcc = insert nspace (fromList dependencies) acc
        in foldr moduleTree newAcc realDeps

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : {auto d : Ref DoneMod (StringMap ())} ->
              {auto o : Ref BuildOrder (List BuildMod)} ->
              ModTree -> Core ()
mkBuildMods mod
    = whenJust (sourceFile mod) $ \ sf =>
            do done <- get DoneMod
               case lookup sf done of
                    Just _ => pure ()
                    Nothing =>
                       do -- build dependencies
                          traverse_ mkBuildMods (deps mod)
                          -- build it now
                          update BuildOrder
                                   (MkBuildMod sf mod.nspace
                                               (map nspace mod.deps) ::)
                          update DoneMod $ insert sf ()

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
-- Return an empty list if it turns out it's in the 'done' list
export
getModTree : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (done : List BuildMod) ->
               (mainFile : String) ->
               Core (Maybe ModTree)
getModTree loc done fname
    = do a <- newRef AllMods []
         fname_ns <- ctxtPathToNS fname
         if fname_ns `elem` map buildNS done
            then pure Nothing
            else map Just (mkModTree {a} loc [] (Just fname) fname_ns)

getModDAG : {auto c : Ref Ctxt Defs} ->
            {auto o : Ref ROpts REPLOpts} ->
            Time =>
            FC -> (done : List BuildMod) ->
            (mainFile : String) ->
            Core (DAG ModuleIdent BuildMod)
getModDAG loc done fname
  = do -- coreLift $ putStrLn "computing mod dag for module file \{fname}"

       Just tree <- withTiming "getModTree" $ getModTree loc done fname
         | Nothing  => pure empty
       dag <- withTiming "modTreeToDAG" $ pure $ modTreeToDAG tree
       -- coreLift $ putStrLn """
       --     dependency tree: \{show dag}
       --     """
       pure dag

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
-- Return an empty list if it turns out it's in the 'done' list
export
getBuildMods : {auto c : Ref Ctxt Defs} ->
               {auto o : Ref ROpts REPLOpts} ->
               FC -> (done : List BuildMod) ->
               (mainFile : String) ->
               Core (List BuildMod)
getBuildMods loc done fname
    = do Just t <- getModTree loc done fname
           | Nothing => pure []
         dm <- newRef DoneMod empty
         o <- newRef BuildOrder []
         mkBuildMods {d=dm} {o} t
         pure (reverse !(get BuildOrder))

checkTotalReq : {auto c : Ref Ctxt Defs} ->
                String -> String -> TotalReq -> Core Bool
checkTotalReq sourceFile ttcFile expected
  = catch (do log "totality.requirement" 20 $
                "Reading totalReq from " ++ ttcFile
              Just got <- readTotalReq ttcFile
                | Nothing => pure False
              log "totality.requirement" 20 $ unwords
                [ "Got", show got, "and expected", show expected ++ ":"
                , "we", ifThenElse (got < expected) "should" "shouldn't"
                , "rebuild" ]
              -- if what we got (i.e. what we used when we checked the file the
              -- first time around) was strictly less stringent than what we
              -- expect now then we need to rebuild.
              pure (got < expected))
          (\error => pure False)

needsBuildingTime : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingTime sourceFile ttcFile depFiles
  = isTTCOutdated ttcFile (sourceFile :: depFiles)

needsBuildingDepHash : {auto c : Ref Ctxt Defs} ->
                 String -> Core Bool
needsBuildingDepHash depFileName
  = catch (do defs                   <- get Ctxt
              depTTCFileName         <- getTTCFileName depFileName "ttc"
              not <$> unchangedHash defs.options.hashFn depTTCFileName depFileName)
          (\error => pure False)

||| Build from source if any of the dependencies, or the associated source file,
||| have been modified from the stored hashes.
needsBuildingHash : {auto c : Ref Ctxt Defs} ->
                    (sourceFile : String) -> (ttcFile : String) ->
                    (depFiles : List String) -> Core Bool
needsBuildingHash sourceFile ttcFile depFiles
  = do defs                <- get Ctxt
       sourceUnchanged <- unchangedHash defs.options.hashFn ttcFile sourceFile
       depFilesHashDiffers <- any id <$> traverse needsBuildingDepHash depFiles
       pure $ (not sourceUnchanged) || depFilesHashDiffers

export
needsBuilding :
  {auto c : Ref Ctxt Defs} ->
  {auto o : ReadOnlyRef ROpts REPLOpts} ->
  (sourceFile, ttcFile : String) -> List String -> Core Bool
needsBuilding sourceFile ttcFile depFiles
  = do -- if the ttc file does not exist there is no point in asking
       -- whether we need to rebuild it
       True <- coreLift $ exists ttcFile
         | False => pure True
       -- check if hash match
       checkHashesInsteadOfTime <- checkHashesInsteadOfModTime <$> getSession
       False <- ifThenElse checkHashesInsteadOfTime
                           needsBuildingHash
                           needsBuildingTime
                  sourceFile ttcFile depFiles
         | True => pure True

       log "import" 20 $ "\{ifThenElse checkHashesInsteadOfTime "Hashes" "Mod Times"} still valid for " ++ sourceFile

       False <- missingIncremental ttcFile
         | True => pure True

       -- in case we're loading the main file, make sure the TTC is
       -- using the appropriate default totality requirement
       Just f <- mainfile <$> read ROpts
         | Nothing => pure False
       log "totality.requirement" 10 $ concat {t = List}
         [ "Checking totality requirement of "
         , sourceFile
         , " (main file is "
         , f
         , ")"
         ]
       let True = sourceFile == f
         | False => pure False
       True <- checkTotalReq sourceFile ttcFile !(totalReq <$> getSession)
         | False => pure False
       -- if it needs rebuilding then remove the buggy .ttc file to avoid going
       -- into an infinite loop!
       Right () <- coreLift $ removeFile ttcFile
         | Left err => throw (FileErr ttcFile err)
       pure True


buildMod : {auto o : Ref ROpts REPLOpts} ->
           (loc : FC) ->
           (opts : Options) ->
           (timings : StringMap (Bool, Integer)) ->
           (current, end : Nat) -> BuildMod ->
           Core (List Error)
buildMod loc opts timings num len mod
   = do defs <- initDefs
        _ <- newRef Ctxt
          ({ options := opts, timings := timings } defs)
        addPrimitives
        lazyActive True; setUnboundImplicits True

        let sourceFile = buildFile mod
        let modNamespace = buildNS mod
        ttcFile <- getTTCFileName sourceFile "ttc"
        -- We'd expect any errors in nsToPath to have been caught by now
        -- since the imports have been built! But we still have to check.
        depFilesE <- traverse (nsToPath loc) (imports mod)
        let (ferrs, depFiles) = partitionEithers depFilesE

        log "import" 20 $ unwords $
          [ "Checking whether to rebuild "
          , sourceFile
          , "(" ++ ttcFile ++ ")"
          , "with dependencies:"
          ] ++ depFiles
        rebuild <- needsBuilding sourceFile ttcFile depFiles

        u <- newRef UST initUState
        m <- newRef MD (initMetadata (PhysicalIdrSrc modNamespace))
        _ <- newRef Syn initSyntax

        errs <- ifThenElse (not rebuild) (pure []) $
           do let pad = minus (length $ show len) (length $ show num)
              let msgPrefix : Doc IdrisAnn
                  = pretty0 (replicate pad ' ') <+> byShow num
                    <+> slash <+> byShow len <+> colon
              let buildMsg : Doc IdrisAnn
                  = pretty0 mod.buildNS
                    <++> parens (pretty0 sourceFile)
              log "import.file" 10 $ "Processing " ++ sourceFile
              process {u} {m} msgPrefix buildMsg sourceFile modNamespace

        ws <- emitWarningsAndErrors (if null errs then ferrs else errs)
        pure (ws ++ if null errs then ferrs else ferrs ++ errs)

export
buildMods : {auto s : Ref Syn SyntaxInfo} ->
            {auto o : Ref ROpts REPLOpts} ->
            (loc : FC) ->
            (opts : Options) ->
            (timings : StringMap (Bool, Integer)) ->
            (current, end : Nat) -> List BuildMod ->
            Core (List Error)
buildMods fc opts timings num len [] = pure []
buildMods fc opts timings num len (m :: ms)
    = case !(buildMod fc opts timings num len m) of
           [] => buildMods fc opts timings (1 + num) len ms
           errs => pure errs

buildModsConcurrent :
    {auto c : Ref Ctxt Defs} ->
    {auto s : Ref Syn SyntaxInfo} ->
    {auto o : Ref ROpts REPLOpts} ->
    (loc : FC) ->
    (opts : Options) ->
    (timings : StringMap (Bool, Integer)) ->
    (taskCount : Nat) ->
    DAG ModuleIdent BuildMod ->
    Core (List Error)
buildModsConcurrent loc opts timings taskCount dag
  = let builder : BuildMod -> IO (Either (List Error) ())
        builder mod =
          coreRun (withLogLevel (mkLogLevel "import.file" 20)
                              $ buildMod loc opts timings 0 taskCount mod)
                  (pure . Left . singleton)
                  (\case [] => pure (Right ()); n => pure (Left n))
    in do
      (_, []) <- coreLift
               $ execConcurrently dag builder opts.session.threads
        | errs => pure (join (snd errs))
      pure []

export
buildDeps : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref MD Metadata} ->
            {auto u : Ref UST UState} ->
            {auto o : Ref ROpts REPLOpts} ->
            (mainFile : String) ->
            Core (List Error)
buildDeps fname
    = do mods <- getBuildMods EmptyFC [] fname
         log "import" 20 $ "Needs to rebuild: " ++ show mods
         (opts, timings) <- readPresistentOpts
         ok <- buildMods EmptyFC opts timings 1 (length mods) mods
         case ok of
              [] => do -- On success, reload the main ttc in a clean context
                       clearCtxt; addPrimitives
                       modIdent <- ctxtPathToNS fname
                       put MD (initMetadata (PhysicalIdrSrc modIdent))
                       mainttc <- getTTCFileName fname "ttc"
                       log "import" 10 $ "Reloading " ++ show mainttc ++ " from " ++ fname
                       readAsMain mainttc

                       -- Load the associated metadata for interactive editing
                       mainttm <- getTTCFileName fname "ttm"
                       log "import" 10 $ "Reloading " ++ show mainttm
                       readFromTTM mainttm
                       pure []
              errs => pure errs -- Error happened, give up

getAllBuildMods : {auto c : Ref Ctxt Defs} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  FC -> (done : List BuildMod) ->
                  (allFiles : List String) ->
                  Core (List BuildMod)
getAllBuildMods fc done [] = pure done
getAllBuildMods fc done (f :: fs)
    = do ms <- getBuildMods fc done f
         getAllBuildMods fc (ms ++ done) fs

getAllModDAG : {auto c : Ref Ctxt Defs} ->
                  {auto o : Ref ROpts REPLOpts} ->
                  Time =>
                  FC -> (done : DAG ModuleIdent BuildMod) ->
                  (allFiles : List String) ->
                  Core (DAG ModuleIdent BuildMod)
getAllModDAG fc done [] = pure done
getAllModDAG fc done (f :: fs)
    = do ms <- withTiming "getModDAG" $ getModDAG fc (values done.items) f
         getAllModDAG fc (merge const ms done) fs

export
buildAll : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           {auto o : Ref ROpts REPLOpts} ->
           (allFiles : List String) ->
           Core (List Error)
buildAll allFiles
    = do
         coreLift $ putStrLn "--- starting compilation of modules ---------------------------"
         _ <- newRef TimeRef empty
         mods <- withTiming "getAllModDAG" $ getAllModDAG EmptyFC empty allFiles
         buildTime <- get TimeRef
         coreLift $ putStrLn """
           build timings:
           \{unlines $ map show $ kvList buildTime}
           """
         -- coreLift $ putStrLn """
         --   compiling files: \{show allFiles}
         --   modules in the tree that are not in the item list:
         --   \{unlines $ map show $ Prelude.toList $ difference (keySet mods.tree) (keySet mods.items)}
         --   final tree before building \{show mods}
         --   """
         (opts, timings) <- readPresistentOpts
         buildModsConcurrent EmptyFC opts timings
           (length $ Prelude.toList mods.items) mods
--     = do mods <- getAllBuildMods EmptyFC [] allFiles
--          -- There'll be duplicates, so if something is already built, drop it
--          let mods' = dropLater mods
--          (opts, timings) <- readPresistentOpts
--          buildMods EmptyFC opts timings 1 (length mods') mods'
  where
    dropLater : List BuildMod -> List BuildMod
    dropLater [] = []
    dropLater (b :: bs)
        = b :: dropLater (filter (\x => buildFile x /= buildFile b) bs)
