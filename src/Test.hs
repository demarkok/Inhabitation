module Test where
import Inhabitation
import Control.Monad.Writer 
import Data.Complex

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


inCurryStyle :: MultiTNF -> String
inCurryStyle (MultiTNF abstractors h applicands)
    | null $ abstractors !! 0 = show h
    | otherwise = 
        (showString "{") . 
        (shows $ length $ (abstractors !! 0)) .
        (showString "}") .
        (showString "(") .
        (shows h) .
        (foldr (.) id $ (showString . showString " ") <$> inCurryStyle <$> applicands) .
        (showString ")") $ 
        ""