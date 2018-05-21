module Test where
import Inhabitation
  
tArr = TVar "a" :-> TVar "a"

tNat = tArr :-> tArr

tBool = TVar "a" :-> TVar "a" :-> TVar "a"


test1 = unMeta [[]] (Meta [tArr])
test2 = unMeta [[]] (Meta [tNat])
test3 = unMeta [[]] (Meta [tBool])

test4 = unMeta [[]] (Meta [((TVar "a" :^: TVar "b") :-> TVar "b") :^: 
                           ((TVar "a" :^: TVar "b") :-> TVar "a")])




