import Control.Arrow (second)
import Control.Monad (guard)
import Data.List (unfoldr)

type Symb = String 

infixr 3 :->  -- type arrow
infixl 4 :^:  -- type intersection

infix 1 <:    -- subtyping     p <: q   <=>    x:p |- x:q

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
          | Type :^: Type   -- пересечение
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

{-
data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизированна
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord) 
-}

data MultiTNF = Meta
                  [Type] -- invariant: this types shouldn't be :^:
              | MultiTNF
                  [Ctx]
                  Int
                  [MultiTNF]

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


-- a -> b -> c          |-->    (c, [b, a])
uncurryArrow2RevList :: Type -> (Type, [Type])
uncurryArrow2RevList = uncurryArrow2RevList' [] where
  uncurryArrow2RevList' :: [Type] -> Type -> (Type, [Type])
  uncurryArrow2RevList' res atom@(TVar _) = (atom, res)
  uncurryArrow2RevList' res inter@(_ :^: _) = (inter, res) 
  uncurryArrow2RevList' res (t1 :-> t2) = uncurryArrow2RevList' (t1 : res) t2

-- a -> b -> (c ^ d)    |-->    [(c, [b, a]), (d, [b, a])]
uncurry2RevList :: Type -> [(Symb, [Type])]
uncurry2RevList atom@(TVar x) = [(x, [])] 
uncurry2RevList t = do
  t' <- removeIntersection t
  let (arrowHead, arrowTail) = uncurryArrow2RevList t'
  (resultingHead, nearestTail) <- removeIntersection arrowHead >>= uncurry2RevList
  return (resultingHead, nearestTail ++ arrowTail)

curryFromList :: (Symb, [Type]) -> Type
curryFromList (h, rest) = (foldr1 (:->) rest) :-> TVar h

curryFromRevList :: (Symb, [Type]) -> Type
curryFromRevList (h, rest) = curryFromList (h, reverse rest)


isArrow :: Type -> Bool
isArrow (_ :-> _) = True
isArrow _ = False

(<:) :: Type -> Type -> Bool
TVar a <: TVar b = a == b
a <: b
  | (sA :-> tA) <- a,
    (sB :-> tB) <- b  = (tA <: tB) && (sB <: sA)
  | otherwise         = all (\t -> any (<:t) a') b' where  -- for all t in b' thers's an s <: t in a'. 
      a' = removeIntersection a
      b' = removeIntersection b


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
  

  -- let (abstractors, ts''') = undefined
    

  -- let revAbstractors = (\(h, t) -> (h, reverse t)) <$> abstractors
  
  let palettes = zipWith (++) abstractors ctxts'' -- context complemented with abstractors

  let palette = palettes  !! shortestTypeInd -- get the full context for the variable
  let (v, []) = ts'''     !! shortestTypeInd -- get the variable name

  (candHead, candHeadInd) <- zip palette [0..] -- choose one possible head from the full context
                                               -- now head isn't expanded

  let expandedCandHead = uncurry2List candHead -- expand the head

  (w, headArgs) <- expandedCandHead            -- choose non-determenistically head of the head =)        
  
  guard $ w == v                               -- check if it's a variable we are looking for

  let k = length headArgs

  -- now we should check if the candHeadInd can produce other `types to inhabit` (from ts''') in other contexts (palettes)
  -- by "producing" we mean that the head takes minArgLen arguments and returns a subtype of the `type to inhabit`

  tails <- sequenceA $ do 
    (subtaskPalette, subtaskType) <- zip palettes  ts'''
    let expandedHeadToCheck = uncurry2List $ subtaskPalette !! candHeadInd
    return $ do 
      (subtW, subtHeadArgs) <- expandedHeadToCheck
      guard $ length subtHeadArgs >= k && ((curryFromRevList (subtW, drop k subtHeadArgs)) <: (curryFromList subtaskType))
      return $ take k subtHeadArgs

  return $ MultiTNF abstractors candHeadInd (Meta <$> tails)




  



{-
-- each TNF has the same structure (but different types in the abstractor)
unMeta :: [(Ctx, TNF)] -> [TNF]
unMeta zetas (TNF ctx h vs) = TNF ctx h <$> traverse (unMeta (ctx ++ zetas)) vs -- each combination of possible meta-replacement for each applicand
unMeta zetas (Meta t) = do
  let (alpha, sigmas) = uncurry2RevList t -- t = sigma_1 -> sigma_2 -> ... -> alpha
  (cand, candInd) <- zip (sigmas ++ zetas) [0..] -- possible candidate which may give us alpha
  let (candHead, candArgs) = uncurry2List cand -- but to get alpha we have to get candidate's arguments somethere
  guard $ candHead == alpha
  return $ TNF sigmas candInd (Meta <$> candArgs) -- let's create meta variables for this!


isTerm :: TNF -> Bool
isTerm (Meta _) = False
isTerm (TNF _ _ applicands) = all isTerm applicands


allTNFGens :: Type -> [[TNF]]
allTNFGens tau = start : unfoldr step start where
  start = [Meta tau] -- A little bit weird, but I can't use unfold1((
  step :: [TNF] -> Maybe ([TNF], [TNF])
  step old
    | all isTerm old = Nothing
    | null new = Nothing -- is Empty
    | otherwise = Just (new, new) where
      new = filter (not. isTerm) old >>= (unMeta [])


inhabGens :: Type -> [[TNF]]
inhabGens = map (filter isTerm) . allTNFGens

inhabs :: Type -> [TNF]
inhabs = concat . inhabGens

-}