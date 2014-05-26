{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# language OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

module CO4.Test.LocalTermination.Run where

import           Control.Monad (when)
import           System.IO (hPutStrLn,stderr)
import qualified TPDB.Data as T
import qualified TPDB.Data as T
import qualified TPDB.DP   as T
import qualified TPDB.CPF.Proof.Type as T hiding (arity)
import qualified TPDB.CPF.Proof.Util as T
import qualified Satchmo.Core.Decode 
import           CO4 hiding (Config)
import           CO4.Prelude
import           CO4.Test.LocalTermination.Util 
import           CO4.Test.LocalTermination.Allocators (allocator)
import           CO4.Test.LocalTermination.Standalone 
import           CO4.Test.LocalTermination.Config
import           CO4.Test.LocalTermination.Proof.Dump (dumpTrs,dump)

$( compileFile [Cache, NoAllocators, ImportPrelude, InstantiationDepth 15] 
   "test/CO4/Test/LocalTermination/Standalone.hs" )

runN :: Config -> T.TRS T.Identifier T.Identifier -> IO Bool
runN config trs =
  if not (isValidTrs original)
  then hPutStrLn stderr "invalid trs" >> return False
  else goDP original
  where
    (original, symbolMap) = fromTPDBTrs $ T.dp trs

    goDP dp = case hasMarkedRule dp of
      False -> return True
      True  -> run1' symbolMap config original dp >>= \case
        Nothing       -> return False
        Just (dp', _) -> goDP dp'

{-
run1 :: Config -> T.TRS T.Identifier (T.Marked T.Identifier) 
     -> IO (Maybe (T.TRS T.Identifier (T.Marked T.Identifier)))
run1 config trs = do
  let (dp@(Trs rules), symbolMap) = fromTPDBTrs trs

  run1' symbolMap config dp >>= \case
    Nothing -> return Nothing
    Just (_, delete) ->
      let trs' = trs { T.rules = do
                         (original, transformed) <- zip (T.rules trs) rules
                         if transformed `elem` delete
                           then []
                           else return original
                     }
      in
        return $ Just trs'
        -}

run1' :: SymbolMap -> Config -> DPTrs ()-> DPTrs () -> IO (Maybe (DPTrs (), [DPRule ()]))
run1' symbolMap config original dp = 
  let mValues   = modelValues $ modelBitWidth config
      automaton = fromTPDBAutomaton symbolMap inputAutomaton
      parameter = (original, dp, mValues, automaton, nat (modelBitWidth config) 0)
      alloc     = allocator config dp
  in do
    when (beVerbose config) $ dumpTrs config symbolMap dp 

    solveAndTestP parameter alloc encConstraint constraint
      >>= \case Nothing -> return Nothing
                Just proof@(Proof model orders) -> 
                  let (labeledTrs,True) = makeLabeledTrs model dp mValues
                      ints              = intermediates dp labeledTrs orders
                      (dp',delete)      = removeMarkedUntagged dp $ last ints
                  in do
                    when (beVerbose $ config) $ dump config symbolMap dp proof
                    return $ Just (dp', delete)

inputAutomaton :: Automaton (T.Marked T.Identifier) State 
inputAutomaton = (states, transition)
  where
    q          = nat 2
    s          = T.Original $ T.mk 0 "S"
    ap         = T.Original $ (\i -> i {T.arity = 2 }) $ T.mk 0 "ap" 
    apStar     = T.Marked   $ (\i -> i {T.arity = 2 }) $ T.mk 0 "ap"
    states     = [ q 0, q 1, q 2 ]
    transition = [ (s , [ ([], q 1) ])
                 , (ap, [ ([q 1, q 1], q 2)
                        , ([q 2, q 1], q 2)
                        , ([q 1, q 2], q 0)
                        , ([q 2, q 2], q 0)

                        , ([q 0, q 0], q 0)
                        , ([q 0, q 1], q 0)
                        , ([q 0, q 2], q 0)

                        , ([q 0, q 0], q 0)
                        , ([q 1, q 0], q 0)
                        , ([q 2, q 0], q 0)
                        ])
                 ]
