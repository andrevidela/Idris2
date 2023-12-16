module Libraries.System.Concurrency.Parallel

import Data.Either
import System.Concurrency

||| The summary of a test pool run
public export
record Summary (result : Type) (error : Type) where
  constructor MkSummary
  success : List result
  failure : List error

||| A new, blank summary
export
initSummary : Summary r e
initSummary = MkSummary [] []

||| Update the summary to contain the given result
export
updateSummary : (newRes : Either e a) -> Summary a e -> Summary a e
updateSummary newRes =
  case newRes of
       Left l  => { failure $= (l ::) }
       Right w => { success $= (w ::) }

||| Update the summary to contain the given results
export
bulkUpdateSummary : (newRess : List (Either e a)) -> Summary a e -> Summary a e
bulkUpdateSummary newRess =
  let (ls, ws) = partitionEithers newRess in
  { success $= (ws ++)
  , failure $= (ls ++)
  }

export
Semigroup (Summary a e) where
  MkSummary ws1 ls1 <+> MkSummary ws2 ls2
    = MkSummary (ws1 ++ ws2) (ls1 ++ ls2)

export
Monoid (Summary a e) where
  neutral = initSummary

||| An instruction to a thread which runs tests
public export
data ThreadInstruction : Type -> Type where
  ||| A test to run
  Run : (identifier : i) -> ThreadInstruction i
  ||| An indication for the thread to stop
  Stop : ThreadInstruction i

||| Sends the given tests on the given @Channel@, then sends `nThreads` many
||| 'Stop' @ThreadInstruction@s to stop the threads running the tests.
|||
||| @testChan The channel to send the tests over.
||| @nThreads The number of threads being used to run the tests.
||| @tests The list of tests to send to the runners/threads.
export
testSender : (testChan : Channel (ThreadInstruction a)) -> (nThreads : Nat)
           -> (tests : List a) -> IO ()
testSender testChan 0 [] = pure ()
testSender testChan (S k) [] =
  -- out of tests, so the next thing for all the threads is to stop
  do channelPut testChan Stop
     testSender testChan k []
testSender testChan nThreads (test :: tests) =
  do channelPut testChan (Run test)
     testSender testChan nThreads tests

||| A result from a test-runner/thread
public export
data ThreadResult : a -> err -> Type where
  ||| The result of running a test
  Res : (value : Either err a) -> ThreadResult a err
  ||| An indication that the thread was told to stop
  Done : ThreadResult a err

||| Receives results on the given @Channel@, accumulating them as a @Summary@.
||| When all results have been received (i.e. @nThreads@ many 'Done'
||| @ThreadInstruction@s have been encountered), send the resulting Summary over
||| the @accChan@ Channel (necessary to be able to @fork@ this function and
||| still obtain the Summary at the end).
|||
||| @resChan The channel to receives the results on.
||| @acc The Summary acting as an accumulator.
||| @accChan The Channel to send the final Summary over.
||| @nThreads The number of threads being used to run the tests.
export
testReceiver : (resChan : Channel (ThreadResult a err)) -> (acc : Summary a err)
             -> (accChan : Channel (Summary a err)) -> (nThreads : Nat) -> IO ()
testReceiver resChan acc accChan 0 = channelPut accChan acc
testReceiver resChan acc accChan nThreads@(S k) =
  do (Res res) <- channelGet resChan
        | Done => testReceiver resChan acc accChan k
     testReceiver resChan (updateSummary res acc) accChan nThreads

||| Function responsible for receiving and running tests.
|||
||| @opts The options to run the threads under.
||| @testChan The Channel to receive tests on.
||| @resChan The Channel to send results over.
testThread : (run : arg -> IO (Either err res)) -> (testChan : Channel (ThreadInstruction arg))
              -> (resChan : Channel (ThreadResult res err)) -> IO ()
testThread run testChan resChan =
  do (Run test) <- channelGet testChan
        | Stop => channelPut resChan Done
     res <- run test
     channelPut resChan (Res res)
     testThread run testChan resChan

export
runParallel : {0 input : Type} ->
              (input -> IO (Either err res)) ->
              List input ->
              (threads : Nat) ->
              IO (Summary res err)
runParallel exec inputs threads = do
       -- set up the channels
       accChan <- makeChannel
       resChan <- makeChannel
       testChan <- makeChannel

       -- and then run all the tests

       for_ [1 .. threads] $ \_ =>
         fork (testThread exec testChan resChan)
       -- start sending tests
       senderTID <- fork $ testSender testChan threads inputs
       -- start receiving results
       receiverTID <- fork $ testReceiver resChan initSummary accChan threads
       -- wait until things are done, i.e. until we receive the final acc
       channelGet accChan
