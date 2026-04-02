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
import Core.Core

public export
record DAG (key: Type) (value : Type) where
  constructor MkDAG
  items : SortedMap key value
  -- For each node, there is a list of children
  tree : SortedMap key (SortedSet key)

export
empty : Ord key => DAG key value
empty = MkDAG empty empty

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

-- Given a list of available children, we produce a new list by combining
-- the existing ones with the new ones
updateAvailableChildren : Ord key => key -> DAG key value -> SortedSet key -> SortedSet key
updateAvailableChildren key dag = union (availableChildren key dag)

allChildren : Ord key => key -> DAG key value -> SortedSet key -> SortedSet key
allChildren key dag acc with (lookup key dag.tree)
  _ | Nothing = acc
  _ | Just children = foldr (\childKey => allChildren childKey dag) (union children acc) children

m2l : Maybe a -> List a
m2l (Just a) = pure a
m2l Nothing = []

(.send) : Channel a -> a -> Core ()
(.send) channel = coreLift . channelPut channel

(.wait) : Channel a -> Core a
(.wait) = coreLift . channelGet

record TaskOutcome (0 key : Type) (0 error : Type) where
  constructor MkOut
  wid : key
  errors : List error

record CoordinatorState (0 key, error : Type) where
  constructor MkSt
  done : Channel (List error)
  availableTasks : SortedSet key
  collectedErrors : List error
  hasFailedDependency : SortedSet key -- dictionary of keys with failed parent keys

updateStateFromOutcome : Show key => Ord key => TaskOutcome key error -> DAG key value -> CoordinatorState key error -> (CoordinatorState key error, Nat)
updateStateFromOutcome (MkOut doneTask []) dag state =
  let doneRemoved = difference state.availableTasks (singleton doneTask)
      newAvailable = updateAvailableChildren doneTask dag doneRemoved
  in -- putStrLn "Coord: provisional list of tasks without the new unlocked tasks:\n\{show doneRemoved}"
  ({ availableTasks := newAvailable} state, Z)
updateStateFromOutcome (MkOut doneTask errors) dag state =
  let doneRemoved = difference state.availableTasks (singleton doneTask)
      toRemove = allChildren doneTask dag empty
      totalAvailable = state.availableTasks `difference` toRemove
  in
  ( { availableTasks := totalAvailable, collectedErrors $= (errors ++)
    , hasFailedDependency $= union toRemove} state
  , length (Prelude.toList toRemove))

parameters {0 key : Type} {0 value : Type} {0 error : Type}
    (task : Channel (Maybe key)) (workNotif : Channel (TaskOutcome key error)) (dag : DAG key value)

  runWorker : Show key => (worker_id : Nat) ->
              (perform : value -> Core (List error)) ->
              Core ()
  runWorker wid perform = do
    coreLift $ putStrLn "Worker \{show wid}: available"
    Just taskKey <- task.wait
      | Nothing => coreLift $ putStrLn "terminating worker \{show wid}" >>
                   pure ()
    coreLift $ putStrLn "Worker \{show wid}: Recieve & perform task \{show taskKey}"
    let value = m2l $ lookup taskKey dag.items
    errs <- traverse perform value
    coreLift $ putStrLn "Worker \{show wid}: sending notification that task is done"
    workNotif.send (MkOut taskKey (join errs))
    runWorker wid perform

  coordinator : Show key => Ord key =>
                Show error =>
                CoordinatorState key error ->
                (availableWorkers : Nat) ->
                (remainingTasks : Nat) ->
                Core ()
  coordinator state Z Z
    = coreLift (putStrLn "Coord: all jobs done, notifying main thread")
    >> state.done.send state.collectedErrors
  coordinator state Z (S remain)
    = do -- no workers available, wait for the next result to keep going
         coreLift $ putStrLn "Coord: no worker available, waiting for next result, \{show $ S remain} tasks remain}"
         outcome <- workNotif.wait
         coreLift $ putStrLn "Coord: task \{show outcome.wid} is finished"
         -- update the list of available jobs given the ones we already have
         -- coordinator runs again with 1 more worker available
         let (newState, count) = updateStateFromOutcome outcome dag state
         coordinator newState 1 (remain `minus` count)
  coordinator state (S w) Z
    = do coreLift $ putStrLn "Coord: No more tasks, killing workers \{show w} left"
         task.send Nothing
         coordinator state w Z
  coordinator state (S availableWorkers) (S remain) with (pop state.availableTasks)
    _ | Nothing
      = do coreLift $ putStrLn "Coord: We have \{show (S remain)} tasks in flight, waiting"
           outcome  <- workNotif.wait
           let (newState, count) = updateStateFromOutcome outcome dag state
           coordinator newState (S availableWorkers) (remain `minus` count)
    _ | Just (next, jobs)
      = do coreLift $ putStrLn "Coord: \{show (S availableWorkers)} workers available, sending task \{show next}, \{show $ S remain} tasks remain"
           if (state.hasFailedDependency `contains'` next)
             then do
               coreLift (putStrLn "skipping task \{show next}, one of its dependencies failed")
               coordinator ({availableTasks := jobs} state) availableWorkers remain
             else do
               task.send (Just next)
               coordinator ({availableTasks := jobs} state) availableWorkers (S remain)

parameters {0 key : Type} {0 value : Type} {0 error : Type}
  {auto ord : Ord key} (perform : value -> Core (List error)) (dag : DAG key value)

  export
  execConcurrently : Show key => Show error => (threads : Nat) -> Core (List error)
  execConcurrently threads = do
    coreLift $ putStrLn "Starting concurrent execution on \{show threads} threads"
    startTime <- coreLift $ clockTime Monotonic
    tasks <- coreLift $ makeChannel
    workNotif <- coreLift $ makeChannel
    done <- coreLift $ makeChannel
    -- spawn the coordinator
    let roots = fromList dag.getRoots
    coreLift $ putStrLn "Starting coordinator with roots \{show roots}"
    let coordinatorInit = MkSt done roots [] empty
    ignore $ coreLift $ fork (coreRun (coordinator tasks workNotif dag coordinatorInit threads dag.nodeCount) ?aqw ?bi)
    -- spawn the workers
    ignore $ for [1 .. threads] $ \n => do
      coreLift $ putStrLn "Spawning worker \{show n}"
      coreLift $ fork (coreRun (runWorker tasks workNotif dag n perform) ?aa pure)

    -- wait until the coordinator runs out of tasks
    errors <- done.wait
    endTime <- coreLift $ clockTime Monotonic
    let duration = endTime `timeDifference` startTime

    -- stop workers
    ignore $ for (replicate threads ()) $ \_ =>
      tasks.send Nothing

    coreLift $ putStrLn "done with time \{show duration}"
    pure errors

export
execConcurrentlyNoError :
  Ord key =>
  Show key =>
  (perform : value -> Core ()) -> DAG key value ->
  (threads : Nat) -> Core ()
execConcurrentlyNoError perform dag threads = ignore $ execConcurrently {error = Void} (map (const []) . perform) dag threads


