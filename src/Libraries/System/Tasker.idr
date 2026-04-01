module Library.System.Tasker

import Data.SortedMap
import Data.SortedSet
import Data.Maybe
import Data.List
import Control.Monad.State
import System.Concurrency
import System.Clock

public export
record DAG (key: Type) (value : Type) where
  constructor MkDAG
  items : SortedMap key value
  -- For each node, there is a list of children
  tree : SortedMap key (SortedSet key)

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

-- to exec the list of tasks in order without multi-threading we supply a list of
-- elements available for computation as the initial state. Then we match on that state
-- and see if there is any available job. If there isn't, we are done. If there are, we
-- pick the next job in the queue, and run it, because it is finished, we all all its children
-- to the list of jobs available to perform, and repeat.
execLinearly : Ord key => (perform : value -> IO ()) -> DAG key value -> StateT (SortedSet key) IO ()
execLinearly perform dag =
  case pop !get of
    Nothing => putStrLn "done"
    Just (key , keys) => do
      let value = lookup key dag.items
      _ <- lift $ traverse perform value
      put (updateAvailableChildren key dag keys)
      execLinearly perform dag

(.send) : Channel a -> a -> IO ()
(.send) = channelPut

(.wait) : Channel a -> IO a
(.wait) = channelGet

parameters {0 key : Type} {0 value : Type}
    (task : Channel (Maybe key)) (workNotif : Channel key) (dag : DAG key value)

  runWorker : Show key => (worker_id : Nat) ->
              (perform : value -> IO ()) ->
              IO ()
  runWorker wid perform = do
    putStrLn "Worker \{show wid}: available"
    Just taskKey <- task.wait
      | Nothing => putStrLn "terminating worker \{show wid}" >>
                   pure ()
    putStrLn "Worker \{show wid}: Recieve & perform task \{show taskKey}"
    let value = lookup taskKey dag.items
    ignore $ traverse perform value
    putStrLn "Worker \{show wid}: sending notification that task is done"
    workNotif.send taskKey
    runWorker wid perform

  coordinator : Show key => Ord key =>
                (done : Channel ()) ->
                (nextTasks : SortedSet key) ->
                (availableWorkers : Nat) ->
                (remainingTasks : Nat) ->
                IO ()
  coordinator doneChannel _ Z Z
    = putStrLn "Coord: all jobs done, notifying main thread" >> doneChannel.send ()
  coordinator doneChannel availableTasks Z (S remain)
    = do -- no workers available, wait for the next result to keep going
         putStrLn "Coord: no worker available, waiting for next result, \{show $ S remain} tasks remain}"
         doneTask <- workNotif.wait
         putStrLn "Coord: task \{show doneTask} is finished"
         -- update the list of available jobs given the ones we already have
         let doneRemoved = difference availableTasks (singleton doneTask)
         putStrLn "Coord: provisional list of tasks without the new unlocked tasks:\n\{show doneRemoved}"
         let newJobs = updateAvailableChildren doneTask dag doneRemoved
         -- coordinator runs again with 1 more worker available
         coordinator doneChannel newJobs 1 remain
  coordinator doneChannel n (S w) Z
    = do putStrLn "Coord: No more tasks, killing workers \{show w} left"
         task.send Nothing
         coordinator doneChannel n w Z
  coordinator doneChannel availableTasks (S availableWorkers) (S remain) with (pop availableTasks)
    _ | Nothing
      = do putStrLn "We have \{show (S remain)} tasks in flight, waiting"
           doneTask <- workNotif.wait
           coordinator doneChannel empty availableWorkers remain
    _ | Just (next, jobs) = do
           putStrLn "Coord: \{show (S availableWorkers)} workers available, sending task \{show next}, \{show $ S remain} tasks remain"
           task.send (Just next)
           coordinator doneChannel jobs availableWorkers (S remain)

parameters {0 key : Type} {0 value : Type} {auto ord : Ord key} (perform : value -> IO ()) (dag : DAG key value)

  export
  execConcurrently : Show key => (threads : Nat) -> IO ()
  execConcurrently threads = do
    startTime <- clockTime Monotonic
    tasks <- makeChannel
    workNotif <- makeChannel
    done <- makeChannel
    -- spawn the coordinator
    ignore $ fork (coordinator tasks workNotif dag done (fromList dag.getRoots) threads dag.nodeCount)
    -- spawn the workers
    ignore $ for [1 .. threads] $ \n => do
      putStrLn "Spawning worker \{show n}"
      fork (runWorker tasks workNotif dag n perform)

    -- wait until the coordinator runs out of tasks
    done.wait
    endTime <- clockTime Monotonic
    let duration = endTime `timeDifference` startTime

    -- stop workers
    ignore $ for (replicate threads ()) $ \_ =>
      tasks.send Nothing

    putStrLn "done with time \{show duration}"

  export
  linear : IO ()
  linear = evalStateT (fromList dag.getRoots) (execLinearly perform dag)

