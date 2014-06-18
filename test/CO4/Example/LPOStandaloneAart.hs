module CO4.Example.LPOStandaloneAart
where

import Prelude hiding (lex,lookup)
import CO4.PreludeNat

type Map k v    = [(k,v)]

type Symbol     = Nat

data Term       = Var Symbol
                | Node Symbol [Term]
                deriving (Show)

data Order      = Gr | Eq | NGe

type Rule       = (Term,Term)
type Trs        = [Rule]
type Precedence = Map Symbol Nat

constraint :: Trs -> Precedence -> Bool
constraint rules precedence = 
  all (\(lhs,rhs) -> lpoAart precedence lhs rhs) rules

lpoEqAart :: Precedence -> Term -> Term -> Bool
lpoEqAart precedence s t = 
  if eqTerm s t then True
  else if lpoAart precedence s t
       then True
       else False

lpoAart :: Precedence -> Term -> Term -> Bool
lpoAart precedence s t = 
  case s of
    Var vs    -> False
    Node f ss ->
      or [ lpoAart1 precedence f ss t
         , lpoAart2 precedence f ss t
         , lpoAart3 precedence f ss t
         ]

lpoAart1 :: Precedence -> Symbol -> [Term] -> Term -> Bool
lpoAart1 precedence f ss t = 
  let go1 pairs = case pairs of
        [] -> False
        p:ps -> case p of 
          (s',t') -> if eqTerm s' t' then go1 ps
                                     else go2 pairs

      go2 pairs = case pairs of
        []   -> False
        p:ps -> case p of
          (s',t') -> if lpoAart precedence s' t'
                     then go3 ps
                     else False

      go3 pairs = case pairs of
        []   -> True
        p:ps -> case p of
          (s',t') -> if lpoAart precedence (Node f ss) t'
                     then go3 ps
                     else False
  in case t of 
      Var _     -> False
      Node g ts -> 
        if eqSymbol f g then go1 (zip ss ts)
                        else False

lpoAart2 :: Precedence -> Symbol -> [Term] -> Term -> Bool
lpoAart2 precedence f ss t = 
  case t of 
    Var _     -> False
    Node g ts -> (eqOrder (ord precedence f g) Gr)
              && (all (\t' -> lpoAart precedence (Node f ss) t') ts)

lpoAart3 :: Precedence -> Symbol -> [Term] -> Term -> Bool
lpoAart3 precedence f ss t = any (\s' -> lpoEqAart precedence s' t) ss

ord :: Precedence -> Symbol -> Symbol -> Order
ord precedence a b = 
  let pa = lookup eqSymbol a precedence
      pb = lookup eqSymbol b precedence
  in
      ordNat pa pb

ordNat :: Nat -> Nat -> Order
ordNat a b = case eqNat a b of
  True  -> Eq
  False -> case gtNat a b of
    True  -> Gr
    False -> NGe

varOccurs :: Symbol -> Term -> Bool
varOccurs var term = case term of
  Var var'  -> eqSymbol var var'
  Node _ ts -> any (varOccurs var) ts

lex :: (a -> b -> Order) -> [a] -> [b] -> Order
lex ord xs ys = case xs of
  [] -> case ys of [] -> Eq
                   _  -> NGe
  x:xs' -> case ys of 
    []    -> Gr
    y:ys' -> case ord x y of 
      Gr  -> Gr
      Eq  -> lex ord xs' ys'
      NGe -> NGe

-- * utilities

lookup :: (k -> k -> Bool) -> k -> Map k v -> v
lookup f k map = case map of
  []   -> undefined
  m:ms -> case m of 
    (k',v) -> case f k k' of
      False -> lookup f k ms
      True  -> v

eqTerm :: Term -> Term -> Bool
eqTerm x y = case x of
  Var u     -> case y of { Var v -> eqSymbol u v; _ -> False }
  Node u us -> case y of
    Node v vs -> (eqSymbol u v) &&
                 (eqList eqTerm us vs)
    _         -> False

eqOrder :: Order -> Order -> Bool
eqOrder x y = case x of
  Gr  -> case y of { Gr  -> True; _ -> False }
  Eq  -> case y of { Eq  -> True; _ -> False }
  NGe -> case y of { NGe -> True; _ -> False }

eqSymbol :: Symbol -> Symbol -> Bool
eqSymbol = eqNat

eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqList f xs ys = case xs of
  []   -> case ys of []   -> True
                     _    -> False
  u:us -> case ys of []   -> False
                     v:vs -> (f u v) && (eqList f us vs)
