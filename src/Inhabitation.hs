module Inhabitation where

import Control.Arrow (second)
import Control.Monad (guard)
import Data.List (unfoldr, transpose)

import Debug.Trace

type Symb = String 

infixr 3 :->  -- type arrow
infixl 4 :^:  -- type intersection
infix  1 <:    -- subtyping     p <: q   <=>    x:p |- x:q

data Type = TVar Symb       -- type atom
          | Type :-> Type   
          | Type :^: Type   
    deriving (Read,Show,Eq,Ord)


type Ctx = [Type] -- context


data MultiTNF = Meta
                  [Type] -- invariant: this types shouldn't be :^:
              | MultiTNF
                  [Ctx]
                  Int
                  [MultiTNF] 
    deriving (Read,Show,Eq,Ord) 


-- (a ^ (b -> c)) ^ d   |-->    [a, b -> c, d]
removeIntersection :: Type -> [Type]
removeIntersection atom@(TVar _)   = [atom]
removeIntersection arrow@(_ :-> _) = [arrow]
removeIntersection (a :^: b)       = [a, b] >>= removeIntersection


-- a -> b -> c          |-->    (c, [a, b])
uncurryArrow2List  :: Type -> (Type, [Type])
uncurryArrow2List atom@(TVar _)   = (atom, [])
uncurryArrow2List inter@(_ :^: _) = (inter, []) 
uncurryArrow2List (t1 :-> t2)     = second (t1 : ) $ uncurryArrow2List t2


-- a -> b -> (c ^ d)    |-->    [(c, [a, b]), (d, [a, b])]
uncurry2List :: Type -> [(Symb, [Type])]
uncurry2List atom@(TVar x) = [(x, [])] 
uncurry2List t = do
  t' <- removeIntersection t
  let (arrowHead, arrowTail) = uncurryArrow2List t'
  (resultingHead, nearestTail) <- removeIntersection arrowHead >>= uncurry2List
  return (resultingHead, arrowTail ++ nearestTail)


curryFromList :: (Symb, [Type]) -> Type
curryFromList (h, rest) = foldr (:->) (TVar h) rest

-- a -> b -> (c ^ d)    |-->    (a -> b -> c) ^ (a -> b -> d)
translate :: Type -> Type
translate = foldl1 (:^:) . map curryFromList . uncurry2List


isArrow :: Type -> Bool
isArrow (_ :-> _) = True
isArrow _ = False


-- TODO: PROVE IT!
(<:) :: Type -> Type -> Bool
TVar a      <: TVar b      = a == b
TVar _      <: (_ :-> _)   = False 
(_ :-> _)   <: TVar _      = False 
(sA :-> tA) <: (sB :-> tB) = (tA <: tB) && (sB <: sA)
a           <: b           = all (\t -> any (<:t) a') b' where  -- for all t in b' there's an s <: t in a'. 
                                a' = removeIntersection $ translate a
                                b' = removeIntersection $ translate b


unMeta :: [Ctx] -> MultiTNF -> [MultiTNF]
unMeta ctxts (MultiTNF abstractors h vs) = MultiTNF abstractors h <$> traverse (unMeta (zipWith (++) abstractors ctxts)) vs
unMeta ctxts (Meta ts) = do
  let ts'     = uncurry2List <$> ts     -- possibly generates new types to inhabite
                                        -- :: [[(Symb, [Type])]]
                                        -- NB: not reversed!
  let ctxts'      = zipWith (<$) ctxts ts'  -- copy the context for each new generated task 
  let ts''        = concat ts'                           
  let ctxts''     = concat ctxts'
  -- now all the types in ts'' have a variable as a head (a_1 -> ... -> a_k -> x, where x is a variable) and
  -- our goal is to find an inhabitant of the type ts''[i] in the context ctxts''[i] for each i

  -- find subtask with the shortest list of arguments.
  let (minArgLen, shortestTypeInd) = minimum $ zip ((length . snd) <$> ts'') [0..]
  
  -- bite minArgLen arguments out of all the subtasks
  -- NB: type order in each abstractor is reversed (in contrast with the order in the normal type notation 1 -> 2 -> 3)
  --     type order in heads (ts''') is normal (1 -> 2 -> 3 -> x)
  let (abstractors, ts''') = unzip $ do
      (x, args) <- ts'' 
      let abstractor  = reverse $ take minArgLen args
      let restType    = (x, drop minArgLen args)
      return (abstractor, restType)
    
  let palettes = zipWith (++) abstractors ctxts'' -- context complemented with abstractors

  let palette = palettes  !! shortestTypeInd -- get the full context for the variable
  let (v, []) = ts'''     !! shortestTypeInd -- get the variable name

  (candHead, candHeadInd) <- zip palette [0..] -- choose one possible head from the full context
                                               -- at this moment head isn't expanded

  let expandedCandHead = uncurry2List candHead -- expand the head

  (w, headArgs) <- expandedCandHead            -- choose non-determenistically head of the head =)     !!!!!!!   
  
  guard $ w == v                               -- check if it's a variable we are looking for



  let k = length headArgs


  -- now we should check if the candHeadInd can produce other `types to inhabit` (from ts''') in other contexts (palettes)
  -- by "producing" we mean that the head takes minArgLen arguments and returns a subtype of the `type to inhabit`

  tails <- sequenceA $ do 
    (subtaskPalette, subtaskType) <- zip palettes  ts'''
    let expandedHeadToCheck = uncurry2List $ subtaskPalette !! candHeadInd
    return $ do 
      (subtW, subtHeadArgs) <- expandedHeadToCheck
      -- trace (show ((curryFromRevList (subtW, drop k subtHeadArgs)))) [()]
      guard $ length subtHeadArgs >= k && ((curryFromList (subtW, drop k subtHeadArgs)) <: (curryFromList subtaskType))
      return $ take k subtHeadArgs


  return $ MultiTNF abstractors candHeadInd (Meta <$> transpose tails) 



isTerm :: MultiTNF -> Bool
isTerm (Meta _) = False
isTerm (MultiTNF _ _ applicands) = all isTerm applicands


size :: MultiTNF -> Int
size (Meta types) = length types
size (MultiTNF abstractors _ _) = length abstractors


allTNFGens :: Type -> [[MultiTNF]]
allTNFGens tau = start : unfoldr step start where
  start = [Meta [tau]]
  step :: [MultiTNF] -> Maybe ([MultiTNF], [MultiTNF])
  step old
    | all isTerm old = Nothing
    | null new = Nothing -- is Empty
    | otherwise = Just (new, new) where
      new = filter (not. isTerm) old >>= (\mtnf -> unMeta (replicate (size mtnf) []) mtnf)


inhabGens :: Type -> [[MultiTNF]]
inhabGens = map (filter isTerm) . allTNFGens


inhabs :: Type -> [MultiTNF]
inhabs = concat . inhabGens