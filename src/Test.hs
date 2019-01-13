module Test where
import Inhabitation
import Control.Monad.Writer 
import Data.Complex

tA = TVar "a"
tArr = TVar "a" :-> TVar "a"
tArrAB = TVar "a" :-> TVar "b"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"

test1 = unMeta [[]] (Meta [tArr])
test2 = unMeta [[]] (Meta [tNat])
test3 = unMeta [[]] (Meta [tBool])
test4 = unMeta [[]] (Meta [((TVar "a" :^: TVar "b") :-> TVar "b") :^: 
                           ((TVar "a" :^: TVar "b") :-> TVar "a")])

test5 = unMeta [[]] (Meta [tArr :^: (tArrAB :-> tArrAB)])

test6 = inhabs (τ1 :^: τ2) where
    τ1 = ((α :-> b) :-> a) :^: 
         ((β :-> c) :-> b) :^:
         ((α :-> d) :-> c) :^:
         ((β :-> e) :-> d) :-> (α :-> β :-> α :-> β :-> e) :-> a
    
    τ2 = ((β :-> b) :-> a) :^:
         ((α :-> c) :-> b) :^:
         ((α :-> d) :-> c) :^:
         ((β :-> e) :-> d) :-> (β :-> α :-> α :-> β :-> e) :-> a
    [a, b, c, d, e] = TVar <$> ["A", "B", "C", "D", "E"]
    [α, β] = TVar <$> ["a", "b"]

test7 = inhabs (TVar "a" :-> TVar "b" :-> TVar "a")


exp_type :: Int -> Type
exp_type n = foldl1 (:^:) (τ <$> [1..n]) where
    τ i = foldr1 (:->) (q i <$> [0..(n + 1)])
    q i j
        | j == 0       = TVar "a"
        | j == (n + 1) = TVar "b"
        | j == i       = TVar "a" :-> TVar "b"
        | j < i        = (TVar "a" :-> TVar "a") :^: (TVar "b" :-> TVar "b")
        | j > i        = TVar "b" :-> TVar "a"

test8 = inhabs $ exp_type 3

test9 = inhabs $ (tA :^: tArr) :-> tA

test10 = inhabs $ tArr :^: (tArr :-> tArr)

test11 = inhabs $ (TVar "a" :-> (TVar "b" :^: TVar "c")) :-> TVar "a" :-> TVar "c"

test12 = inhabs $ α:^:β :-> γ:^:δ :-> c :-> one where
    [a, b, c, one, two] = TVar <$> ["a", "b", "c", "1", "2"]
    α = ((a :-> a) :-> one) :^: ((b :-> a) :-> two) :-> one
    β = ((a :-> b) :-> one) :^: ((b :-> b) :-> two) :-> two
    γ = ((c :-> a) :-> a) :-> one
    δ = ((c :-> b) :-> a) :-> two

test13 = inhabs $ (TVar "a" :-> TVar "a") :^: ((TVar "a" :-> TVar "b") :-> (TVar "a" :-> TVar "b"))

test14 = inhabs $ (TVar "d" :^: (TVar "a" :-> TVar "e2" :^: (TVar "b" :-> TVar "e3" :^: TVar "c"))) :-> (TVar "d" :^: (TVar "a" :-> TVar "b" :-> TVar "c"))

test15 = inhabs $ (TVar "d" :^: (TVar "a" :-> (TVar "b" :^: TVar "c"))) :->  (TVar "d" :^: (TVar "a" :-> TVar "c"))



inCurryStyle :: MultiTNF -> String
inCurryStyle (MultiTNF abstractors h applicands)
    | null $ abstractors !! 0 = beginPar . (shows h) . (showApp applicands) . endPar $ ""
    | otherwise = 
        (showString "{") . 
        (shows $ length $ (abstractors !! 0)) .
        (showString "}") .
        (showString "(") .
        (shows h) .
        (showApp applicands) .
        (showString ")") $ 
        ""  where
        [beginPar, endPar] = if (null applicands) then [id, id] else showString <$> ["(", ")"]
        showApp l = foldr (.) id $ (showString . showString " ") <$> inCurryStyle <$> applicands
