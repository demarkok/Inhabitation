import Control.Arrow (second)
import Control.Monad (guard)
import Data.List (unfoldr)

type Symb = String 

infixr 3 :->
infixl 4 :^:

data Type = TVar Symb      -- типовой атом
          | Type :-> Type  -- стрелочный тип
          | Type :^: Type   -- пересечение
    deriving (Read,Show,Eq,Ord)

type Ctx = [Type] -- контекст

data TNF = Meta   -- метапеременная (пока еще бесструктурная часть схемы)
             Type   -- типизированна
         | TNF    -- структурированная часть схемы
             Ctx    -- абстрактор 
             Int    -- головная переменная как индекс Де Брауна
             [TNF]  -- бёмовы хвостики
    deriving (Read,Show,Eq,Ord) 

-- a ^ (b -> c) ^ d    |-->    [a, b -> c, d]
removeIntersection :: Type -> [Type]
removeIntersection atom@(TVar _)   = [atom]
removeIntersection arrow@(_ :-> _) = [arrow]
removeIntersection (a :^: b)       = [a, b] >>= removeIntersection

-- a -> b -> c        |-->    (c, [a, b])
uncurryArrow2List  :: Type -> (Type, [Type])
uncurryArrow2List atom@(TVar _)   = (atom, [])
uncurryArrow2List inter@(_ :^: _) = (inter, []) 
uncurryArrow2List (t1 :-> t2)     = second (t1 : ) $ uncurryArrow2List t2

-- a -> b -> (c ^ d)  |-->    [(c, [a, b]), (d, [a, b])]
uncurry2List :: Type -> [(Symb, [Type])]
uncurry2List atom@(TVar x) = [(x, [])] 
uncurry2List t = do
  t' <- removeIntersection t
  let (arrowHead, arrowTail) = uncurryArrow2List t'
  (resultingHead, nearestTail) <- removeIntersection arrowHead >>= uncurry2List
  return (resultingHead, arrowTail ++ nearestTail)


-- a -> b -> c        |-->    (c, [b, a])
uncurryArrow2RevList :: Type -> (Type, [Type])
uncurryArrow2RevList = uncurryArrow2RevList' [] where
  uncurryArrow2RevList' :: [Type] -> Type -> (Type, [Type])
  uncurryArrow2RevList' res atom@(TVar _) = (atom, res)
  uncurryArrow2RevList' res inter@(_ :^: _) = (inter, res) 
  uncurryArrow2RevList' res (t1 :-> t2) = uncurryArrow2RevList' (t1 : res) t2

-- a -> b -> (c ^ d)  |-->    [(c, [b, a]), (d, [b, a])]
uncurry2RevList :: Type -> [(Symb, [Type])]
uncurry2RevList atom@(TVar x) = [(x, [])] 
uncurry2RevList t = do
  t' <- removeIntersection t
  let (arrowHead, arrowTail) = uncurryArrow2RevList t'
  (resultingHead, nearestTail) <- removeIntersection arrowHead >>= uncurry2RevList
  return (resultingHead, nearestTail ++ arrowTail)

{-

-- 

unMeta :: Ctx -> TNF -> [TNF]
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