module CO4.Test.TermComp2014.Allocators
where

import           Control.Exception (assert)
import qualified Data.Map as M
import           CO4.AllocatorData (Allocator,constructors,known)
import           CO4.Prelude (kList,uList,kList',kBool,kTuple2)
import           CO4.PreludeNat (nat,kNat',uNat)
import           CO4.Util (bitWidth)
import           CO4.Test.TermComp2014.Standalone (Symbol,Domain,DPTrs,MarkedSymbol,Label)
import           CO4.Test.TermComp2014.Util (nodeArities)
import           CO4.Test.TermComp2014.Config

allocator :: Config -> DPTrs () -> Allocator
allocator config dpTrs = 
  kTuple2 (modelAllocator config dpTrs)
          (kList (numPrecedences config) $ kTuple2 (filterAllocator     config dpTrs)
                                                   (precedenceAllocator config dpTrs))

filterAllocator :: Config -> DPTrs () -> Allocator
filterAllocator config = kList' . concatMap goArity . M.toList . nodeArities
  where
    n                 = modelBitWidth config
    height            = 2^n
    labels            = map (nat n) [0..height-1]
    goArity (s,arity) = do
      args <- sequence $ replicate arity labels
      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator s) (kLabelAllocator args))
             $ if bruteFilter config
               then kList' []
               else uList arity $ goIndex $ arity - 1

    goIndex 0         = known 0 2 [ ]
    goIndex i         = constructors [ Just [], Just [ goIndex $ i - 1 ] ]

modelAllocator :: Config -> DPTrs () -> Allocator
modelAllocator config = kList' . map goArity . M.toList . nodeArities
  where
    goArity (sym@(_,marked),arity) = kTuple2 (kMarkedSymbolAllocator sym) $
      if marked 
      then kList' [ kTuple2 (kList' [kPattern Nothing]) (kValueAllocator $ nat 0 0) ]
      else goInterpretation arity

    goInterpretation arity = if (numPatterns config) <= 0 || 
                                (numPatterns config) >= interpretationSize
                             then completeInterpretation
                             else incompleteInterpretation
      where
        domainSize         = 2^(modelBitWidth config)
        interpretationSize = domainSize ^ arity

        completeInterpretation = kList' $ do args <- sequence $ replicate arity [0..domainSize - 1]
                                             return $ goMapping args
          where 
            goMapping args = 
              kTuple2 (kList' $ map (kPattern . Just . kValueAllocator 
                                              . nat (modelBitWidth config) 
                                              . fromIntegral) args)
                      (uValueAllocator $ modelBitWidth config)

        incompleteInterpretation = kList (numPatterns config) goMapping
          where
            goMapping = kTuple2 (kList arity $ uPattern $ uValueAllocator $ modelBitWidth config)
                                (uValueAllocator $ modelBitWidth config)

uPattern :: Allocator -> Allocator
uPattern k = constructors [ Just [], Just [k] ]

kPattern :: Maybe Allocator -> Allocator
kPattern alloc = case alloc of
  Nothing -> known 0 2 []
  Just a  -> known 1 2 [ a ]

precedenceAllocator :: Config -> DPTrs () -> Allocator
precedenceAllocator config trs = kList' $ concatMap goArity arities
  where
    arities                = M.toList $ nodeArities trs
    n                      = modelBitWidth config
    height                 = 2^n
    labels                 = map (nat n) [0..height-1]
    precedenceBitWidth     =
      if precedenceDomainBitWidth config < 0
      then bitWidth $ sum $ map (\(_,arity) -> height^arity) arities
      else precedenceDomainBitWidth config

    goArity (symbol,arity) = do
      args <- sequence $ replicate arity labels
      return $ kTuple2 (kTuple2 (kMarkedSymbolAllocator symbol) 
                                (kLabelAllocator args)
                       ) 
                       (uNat precedenceBitWidth)

kValueAllocator :: Domain -> Allocator
kValueAllocator = kNat'
  
uValueAllocator :: Int -> Allocator
uValueAllocator = uNat

kSymbolAllocator :: Symbol -> Allocator
kSymbolAllocator s = assert (not $ null s) $ kList' $ map kBool s

kMarkedSymbolAllocator :: MarkedSymbol -> Allocator
kMarkedSymbolAllocator (s,m) = kTuple2 (kSymbolAllocator s) (kBool m)

kLabelAllocator :: Label -> Allocator
kLabelAllocator = kList' . map kValueAllocator

uLabelAllocator :: Int -> Int -> Allocator
uLabelAllocator n numArgs = kList numArgs $ uValueAllocator n
