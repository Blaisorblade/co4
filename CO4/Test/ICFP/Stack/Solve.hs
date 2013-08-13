{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module CO4.Test.ICFP.Stack.Solve
where

import           Language.Haskell.TH (runIO)
import qualified Satchmo.Core.SAT.Minisat
import qualified Satchmo.Core.Decode 
import           CO4
import           CO4.Prelude

$( compileFile [ImportPrelude, Cache] "CO4/Test/ICFP/Stack/Standalone.hs" )

uOp0 = constructors $ replicate 3 $ Just []
uOp1 = constructors $ replicate 6 $ Just []
uOp2 = constructors $ replicate 4 $ Just []
uOp3 = constructors $ replicate 1 $ Just []

uStatement = constructors [ Just [ uOp0 ] , Just [ uOp1 ] , Just [ uOp2 ], Just [ uOp3 ] ]

uProgram length = constructors [ Just [ kList length uStatement ] ]

allocator = uProgram 16

-- | progressively increase the number of samples
result :: [(Integer,Integer)] -> IO (Maybe String)
result allSamples = iteration 2 2
  where
    iteration numSamples stepping = do
      let mapSample (x,y) = (nat 64 x, nat 64 y)
          samples'        = map mapSample $ take numSamples allSamples
      putStrLn $ unwords $ [ "CO4 solver using", show(length samples')
                         , "samples" ] ++ map show samples'
      out <- solveAndTestP samples' allocator encConstraint constraint
      case out of
          Nothing -> return Nothing
          Just p  -> if constraint (map mapSample allSamples) p
                     then return $ Just $ pretty p
                     else iteration (numSamples + stepping) (stepping + 0)

-- * pretty printing
class Pretty a where
  pretty :: a -> String

instance Pretty Program where
  pretty (Program bs) = "(lambda ( x ) " ++ prog bs  [] ++  ")"


prog :: [Statement] -> [String] -> String
prog bs stack = case bs of
    [] -> case stack of
        [s] -> s
    b : bs' ->  case b of
        Op0 op0 -> prog bs' ( pretty op0 : stack )
        Op1 Nop -> prog bs' stack
        Op1 op1 -> prog bs' ( paren [ pretty op1, stack !! 0 ] : drop 1 stack )
        Op2 op2 -> prog bs' ( paren [ pretty op2, stack !! 1, stack !! 0] : drop 2 stack)
        Op3 op3 -> prog bs' ( paren [ pretty op3, stack !! 2, stack !! 1, stack !! 0] : drop 3 stack)

paren xs = "(" ++ unwords xs ++ ")"

instance Pretty Statement where
  pretty b = case b of
      Op0 op0 -> pretty op0
      Op1 op1 -> pretty op1
      Op2 op2 -> pretty op2

instance Pretty Op0 where
  pretty Null           = "0"
  pretty One            = "1"
  pretty Id           = "x"
  
instance Pretty Op1 where
  pretty Not   = "not"
  pretty Shl1  = "shl1"
  pretty Shr1  = "shr1"
  pretty Shr4  = "shr4"
  pretty Shr16 = "shr16"

instance Pretty Op2 where
  pretty And  = "and"
  pretty Or   = "or"
  pretty Xor  = "xor"
  pretty Plus = "plus"

instance Pretty Op3 where
  pretty If0  = "if0"


{-- mit fold und if
uId  = constructors [ Just [], Just [], Just [] ]
uOp1 = constructors [ Just [], Just [], Just [], Just [], Just [] ]
uOp2 = constructors [ Just [], Just [], Just [], Just [] ]

uE 0 = constructors [ Just [], Just [], Just [ uId ]
                    , Nothing, Nothing, Nothing, Nothing ]

uE i = constructors [ Just [], Just [], Just [ uId ]
                    , Just [ uE (i-1), uE (i-1), uE (i-1) ]
                    , Just [ uE (i-1), uE (i-1), uE (i-1) ]
                    , Just [ uOp1, uE (i-1) ]
                    , Just [ uOp2, uE (i-1), uE (i-1) ]
                    ]

uP depth = constructors [ Just [ uE depth ] ]
<<<<<<< HEAD
-}
