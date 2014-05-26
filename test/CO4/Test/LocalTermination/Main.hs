{-# LANGUAGE LambdaCase #-}
import           System.Exit (exitSuccess, exitFailure)
import           Control.Monad (when)
import           CO4.Test.LocalTermination.Config (parseConfig)
import           CO4.Test.LocalTermination.Run (runN)
import           TPDB.Input (get_trs)

main :: IO ()
main = do
  (config,filePath) <- parseConfig
  trs               <- get_trs filePath 
  runN config trs >>= \case
    False -> do putStrLn "MAYBE" 
                exitFailure

    True  -> do putStrLn "YES"
                exitSuccess
