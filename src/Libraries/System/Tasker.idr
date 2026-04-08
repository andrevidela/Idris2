module Libraries.System.Tasker

import public Data.SortedMap
import public Data.SortedSet
import Data.String
import Data.Maybe
import Data.List
import Control.Monad.State
import System.Concurrency
import System.Clock
import System

import Debug.Trace

public export
record DAG (key: Type) (value : Type) where
  constructor MkDAGFull
  items : SortedMap key value
  -- For each node, there is a list of children
  tree : SortedMap key (SortedSet key)
  -- For each node, there is a list of its parents
  reverseTree : SortedMap key (SortedSet key)

keyInTree : key -> SortedMap key a -> Bool
keyInTree key tree = contains key (keySet tree)

(.allParents) : Ord key => DAG key value -> SortedSet key
dag.allParents = foldr union empty (values dag.reverseTree)
-- check that for all node they have a parent in the tree
export
isConsistent : Ord key => Show key => SortedMap key (SortedSet key) -> Bool
isConsistent parentTree =
  let allParents = foldr union empty (values parentTree)
  in all (\x => keyInTree x parentTree) allParents

export
Show key => Show (DAG key value) where
  show dag = unlines $ map show (kvList dag.reverseTree)

export
empty : Ord key => DAG key value
empty = MkDAGFull empty empty empty


export
(.getItems) : DAG key value -> SortedMap key value
(.getItems) (MkDAGFull i _ _) = i

export
(.getTree) : DAG key value -> SortedMap key (SortedSet key)
(.getTree) (MkDAGFull _ t _) = t

export
(.getReverseTree) : DAG key value -> SortedMap key (SortedSet key)
(.getReverseTree) (MkDAGFull _ _ t) = t

(.getParents) : Ord key => DAG key value -> key -> SortedSet key
dag.getParents key = fromMaybe empty (lookup key dag.reverseTree)

allParents : key -> SortedMap key (SortedSet key) -> List key
allParents key tree =
  let ls = kvList tree
      parentKeys = filter (\(k, v) => v `contains'` key) ls
  in map fst parentKeys

export
invertTree : Ord key => SortedMap key (SortedSet key) -> SortedMap key (SortedSet key)
invertTree tree =
  let keys = keys tree
  in fromList $ map (\key => MkPair key $ fromList $ allParents key tree) keys

export
MkDAG : Ord key => (items : SortedMap key value) -> (tree : SortedMap key (SortedSet key)) -> DAG key value
MkDAG items tree = MkDAGFull items tree (invertTree tree)

export
MkDAG' : Ord key => (items : SortedMap key value) -> (tree : SortedMap key (SortedSet key)) -> DAG key value
MkDAG' items tree = MkDAGFull items (invertTree tree) tree

export
merge : Ord key => (combine : value -> value -> value) -> (l, r : DAG key value) -> DAG key value
merge f l r = MkDAG' (mergeWith f l.items r.items)
    (mergeWith union l.reverseTree r.reverseTree)

maybeLeft : Maybe a -> Either a ()
maybeLeft (Just x) = Left x
maybeLeft _ = Right ()

(.nodeCount) : DAG key value -> Nat
dag.nodeCount = length (keys dag.items)

(.getRoots) : Ord key => DAG key value -> List key
dag.getRoots =
  let allKeys = keys dag.items
      allChildren = foldr union empty (values dag.tree)
  in filter (not . contains' allChildren) allKeys

export
fromList : Ord key => (ls : List (key, value)) -> DAG key value
fromList xs = MkDAG (fromList xs) (fromListLoop xs )
  where
    fromListLoop : List (key, value) -> SortedMap key (SortedSet key)
    fromListLoop xs = fromList (map (mapSnd (const empty)) xs)

export
fromListShow : Show value => (ls : List value) -> DAG String value
fromListShow xs = fromList (map (\x => (show x, x)) xs)

-- total shortcut to obtain the list of children a node points to
availableChildren : Ord key => key -> DAG key value -> SortedSet key
availableChildren key dag
  = fromMaybe empty (lookup key dag.tree)

-- Given the key for a node that just finished. We inspect all it's children and return the ones
-- which parents have all completed
export
updateAvailableChildren :
  {0 key : Type} -> Show key => Ord key =>
  key -> (finished : SortedSet key) ->
  DAG key value -> List key -> List key
updateAvailableChildren doneKey finished dag = let
  -- given a child key, get its parents but remove
  -- the ones that have already been computed
  filterParentsTodo : key -> SortedSet key
  filterParentsTodo childKey =
    let nodeParents = dag.getParents childKey
        diff = difference nodeParents (singleton doneKey `union` finished)
    in diff

  -- The only nodes we check are the children of the node that was just
  -- done. There is no point in checking for any other since they don't
  -- have this node as parent dependency.
  candidateChildren := Prelude.toList $ availableChildren doneKey dag

  -- A node becomes available once all its parent dependencies are computed
  -- for us it means the associated parent set is empty after we remove the
  -- computed nodes
  newlyAvailable := List.filter (Prelude.null . filterParentsTodo) candidateChildren
  in union newlyAvailable

allChildren : Ord key => key -> DAG key value -> SortedSet key -> SortedSet key
allChildren key dag acc with (lookup key dag.tree)
  _ | Nothing = acc
  _ | Just children = foldr (\childKey => allChildren childKey dag) (union children acc) children

m2l : Maybe a -> List a
m2l (Just a) = pure a
m2l Nothing = []

-- to exec the list of tasks in order without multi-threading we supply a list of
-- elements available for computation as the initial state. Then we match on that state
-- and see if there is any available job. If there isn't, we are done. If there are, we
-- pick the next job in the queue, and run it, because it is finished, we all all its children
-- to the list of jobs available to perform, and repeat.
-- execLinearly :
--     Show error => Ord key =>
--     (perform : value -> IO (Maybe error)) -> DAG key value ->
--     StateT (List key, List error) IO (List error)
-- execLinearly perform dag = do
--   (tasks, errors) <- get
--   case tasks of
--     [] => case errors of
--                     [] => putStrLn "done" >> pure []
--                     n => putStrLn "failed with errors:\n\{unlines $ map show n}" >> pure n
--     (key :: keys) => do
--       let value = lookup key dag.items
--       error <- lift $ traverse perform value
--       let newChildren = updateAvailableChildren key dag keys
--       put (newChildren, m2l (join error) ++ errors) -- (newChildren, join error ++ errors)
--       execLinearly perform dag
--
-- export
-- linear : Ord key => Show error => (perform : value -> IO (Maybe error)) -> DAG key value -> IO ()
-- linear perform dag
--   = case !(evalStateT (dag.getRoots, []) (execLinearly perform dag)) of
--               [] => pure ()
--               xs => putStrLn "failed with errors \{show xs}"

(.send) : Channel a -> a -> IO ()
(.send) = channelPut

(.wait) : Channel a -> IO a
(.wait) = channelGet

record TaskOutcome (0 key, error, result : Type) where
  constructor MkOut
  wid : key -- work ID
  outcome : Either error result

record CoordinatorState (0 key, error, result : Type) where
  constructor MkSt
  done : Channel (List result, List error)
  availableTasks : List key
  finishedTasks : SortedMap key result
  collectedErrors : List error
  hasFailedDependency : SortedSet key -- dictionary of keys with failed parent keys

updateStateFromOutcome : Show key => Ord key => TaskOutcome key error result ->
    DAG key value -> CoordinatorState key error result -> (CoordinatorState key error result, Nat)
updateStateFromOutcome (MkOut doneTask (Right resultValue)) dag state =
  let doneRemoved = delete doneTask state.availableTasks
      newAvailable = updateAvailableChildren doneTask (fromList $ keys state.finishedTasks) dag doneRemoved
  in -- putStrLn "Coord: provisional list of tasks without the new unlocked tasks:\n\{show doneRemoved}"
  ({ availableTasks := newAvailable, finishedTasks $= insert doneTask resultValue} state, Z)
updateStateFromOutcome (MkOut doneTask (Left error)) dag state =
  let doneRemoved = delete doneTask state.availableTasks
      toRemove = allChildren doneTask dag empty
      totalAvailable = filter (\x => not (elem x toRemove)) state.availableTasks
  in
  ({ availableTasks := totalAvailable,
     collectedErrors $= (error ::),
     hasFailedDependency $= union toRemove}
  state, S $ length (Prelude.toList toRemove))

parameters {0 key : Type} {0 value : Type} {0 error : Type} {0 result : Type}
    (task : Channel (Maybe (key, value))) (workNotif : Channel (TaskOutcome key error result)) (dag : DAG key value)

  runWorker : Show key => Show error => (worker_id : Nat) ->
              (perform : value -> IO (Either error result)) ->
              IO ()
  runWorker wid perform = do
    -- putStrLn "Worker \{show wid}: available"
    Just (taskKey, taskData) <- task.wait
      | Nothing => -- putStrLn "terminating worker \{show wid}" >>
                   pure ()
    -- putStrLn "Worker \{show wid}: Recieve & perform task \{show taskKey}"
    errs <- perform taskData
    case errs of
         Left e => putStrLn "Worker \{show wid}: sending notification that task \{show taskKey} has failed with error \{show e}"
         Right _ => putStrLn "Worker \{show wid}: sending notification that task \{show taskKey} is finished successfully"
    workNotif.send (MkOut taskKey errs)
    runWorker wid perform

  coordinator : Show key => Ord key =>
                Show error =>
                (allWorkers : Nat) ->
                CoordinatorState key error result ->
                (availableWorkers : Nat) ->
                (remainingTasks : Nat) ->
                IO ()
  coordinator all state Z Z
    = -- putStrLn "Coord: all jobs done, notifying main thread" >>
      state.done.send (values state.finishedTasks, state.collectedErrors)
  coordinator all state Z (S remain)
    = do -- no workers available, wait for the next result to keep going
         -- putStrLn "Coord: no worker available, waiting for next result, \{show $ S remain} tasks remain}"
         outcome <- workNotif.wait
         -- putStrLn "Coord: task \{show outcome.wid} is finished"
         -- update the list of available jobs given the ones we already have
         -- coordinator runs again with 1 more worker available
         let (newState, count) = updateStateFromOutcome outcome dag state
         coordinator all newState 1 (remain `minus` count)
  coordinator all state (S w) Z
    = do -- putStrLn "Coord: No more tasks, killing workers \{show w} left"
         task.send Nothing
         coordinator all state w Z
  coordinator all state (S availableWorkers) (S remain) with (state.availableTasks)
    _ | []
     = if all == S availableWorkers
          then putStrLn """
                 Deadlock detected: All workers are available but we don't have any available task
                 This is often due to a misconfigured initial state where some dependencies are impossible to fulfill.
                 Here is the execution graph you gave me : \{show dag}
                 Here are the dependencies that blocking:
                 \{unlines $ map show $ Prelude.toList $ difference dag.allParents (keySet state.finishedTasks)}
                 Here are the nodes that are unfulfillable:
                 \{unlines $ map show $ filter (\(k, _) => not $ contains k (keySet state.finishedTasks)) (kvList dag.reverseTree)}
                 Shutting down.
                 """
             >> coordinator all state Z Z
          else do
                 -- putStrLn "Coord: We have \{show (S remain)} tasks in flight, waiting"
                 outcome  <- workNotif.wait
                 -- putStrLn "Coord: task \{show outcome.wid} is finished"
                 -- A worker just freed up, so bump the available-worker count.
                 let (newState, count) = updateStateFromOutcome outcome dag state
                 coordinator all newState (S (S availableWorkers)) (remain `minus` count)
    _ | (next :: jobs)
      = -- putStrLn "Coord: \{show (S availableWorkers)} workers available, sending task \{show next}, \{show $ S remain} tasks remain"
        -- >>
        if (state.hasFailedDependency `contains'` next)
              then do
                putStrLn "skipping task \{show next}, one of its dependencies failed"
                coordinator all ({availableTasks := jobs} state) availableWorkers remain
              else do
                let Just value = lookup next dag.items
                  | Nothing => putStrLn """
                      Attempted to read key \{show next} but there is no such key in tree \{show $ keys dag.items}
                      All keys in dag: \{show $ keys dag.tree}
                      Shutting down.
                      """
                      >> coordinator all state (S availableWorkers) Z
                task.send (Just (next, value))
                coordinator all ({availableTasks := jobs} state) availableWorkers (S remain)

parameters {0 key : Type} {0 value : Type} {0 error : Type}
  {auto ord : Ord key} (dag : DAG key value)

  export
  execConcurrently : (perform : value -> IO (Either error result)) ->
                     {default empty alreadyDone : SortedMap key result} ->
                     Show key => Show error => (threads : Nat) -> IO (List result, List error)
  execConcurrently perform threads = do
    -- putStrLn "Starting concurrent execution on \{show threads} threads"
    startTime <- clockTime Monotonic
    tasks <- makeChannel
    workNotif <- makeChannel
    done <- makeChannel
    -- spawn the coordinator
    let roots = dag.getRoots
    -- putStrLn "Starting coordinator with roots \{show roots}"
    let coordinatorInit = MkSt done roots alreadyDone [] empty
    ignore $ fork (coordinator tasks workNotif dag threads coordinatorInit threads dag.nodeCount)
    -- spawn the workers
    ignore $ for [1 .. threads] $ \n => do
      -- putStrLn "Spawning worker \{show n}"
      fork (runWorker tasks workNotif dag n perform)

    -- wait until the coordinator runs out of tasks
    -- (the coordinator already shuts each worker down with a Nothing in its
    -- termination loop, so no extra Nothings are needed here)
    errors <- done.wait
    endTime <- clockTime Monotonic
    let duration = endTime `timeDifference` startTime

    putStrLn "done with time \{show duration}"
    pure errors

  export
  execConcurrently' : (perform : value -> IO (Maybe error)) ->
                     Show key => Show error => (threads : Nat) -> IO (List error)
  execConcurrently' perform n = snd <$> execConcurrently {result = ()}(map maybeLeft . perform) n


export
execConcurrentlyNoError :
  Ord key =>
  Show key =>
  (perform : value -> IO ()) -> DAG key value ->
  (threads : Nat) -> IO ()
execConcurrentlyNoError perform dag threads =
  ignore $ execConcurrently {error = Void} dag (map Right . perform) threads


