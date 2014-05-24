{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# language OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module CO4.Test.LocalTermination.RunA where

import           Control.Monad (when)
import           System.IO (hPutStrLn,stderr)
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.LocalTermination.UtilA
import           CO4.Test.LocalTermination.AllocatorsA
import           CO4.Test.LocalTermination.StandaloneA
import           CO4.Test.LocalTermination.Config

$( compileFile [Cache, NoAllocators, ImportPrelude, InstantiationDepth 15, Dump "/tmp/automaton"] "test/CO4/Test/LocalTermination/StandaloneA.hs" )

run :: Config -> Automaton String State -> IO ()
run config stringAutomaton = 
  let (automaton,symMap) = fromStringAutomaton stringAutomaton
      parameter          = (automaton, nat (automatonStateBitWidth config) 0)
      allocator          = automatonAllocator config automaton
  in
    solveAndTestP parameter allocator encConstraint constraint
      >>= \case Nothing -> putStrLn "Nothing"
                Just a  -> putStrLn $ show $ toStringAutomaton symMap a

test = run (defaultConfig { automatonStateBitWidth = 2 })
           ( [q 1, q 2, q 3]
           , [ ("a", [ ([], q 1) ])
             , ("f", [ ([q 1, q 1], q 2)
                     , ([q 1, q 2], q 3)
                     , ([q 1, q 2], q 3)
                     ]
               )
             ]
           )
  where q = nat 2
           
