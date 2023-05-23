{-# LANGUAGE OverloadedLists #-}

module MyLib (orderSGS, eltsSGS, graphAuts, Graph(..), Permutation(..)) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe
import Data.Monoid()

{-Important types and functions-}
-- |Definition of a (hyper)graph
data Graph a = G (S.Set a) (S.Set (S.Set a)) deriving (Eq, Ord, Show)

-- |Definition of a permutation
newtype Permutation a = P (M.Map a a) deriving (Eq,Ord,Show)

-- |Data structure organising the search of generating permutations
-- The boolean indicates whether or not this is a terminal / solution node
data SearchTree a = T Bool a [SearchTree a] deriving (Eq, Ord, Show, Functor)


-- |Given a graph, return the strong generating set
graphAuts :: (Ord a) => Graph a -> [Permutation a]
graphAuts g = filter (/=mempty) (strongTerminals (gAutsDPT g))

-- |Given a strong generating set, return the order of the group it generates.
-- Note that the SGS is assumed to be relative to the natural order of the points on which the group acts.
orderSGS :: (Ord a) => [Permutation a] -> Integer
orderSGS sgs = product $ map (L.genericLength . fundamentalOrbit) bs where
    bs = toListSet $ map minsupp sgs
    fundamentalOrbit b = b .^^ filter ( (b <=) . minsupp ) sgs

-- |Given a strong generating set, return elements of the group it generates.
-- At first, we calculate transversal transversal generating set and only then return elements of the group  
eltsSGS :: (Ord a)=> [Permutation a]->[Permutation a]
eltsSGS sgs=eltsTGS (tgsFromSgs sgs)

-- |Return a strong generating set ftrom the whole search tree. 
-- For example, if we have already found (3 4), and then we find (1 2 3),
-- then there is no need to look for (1 3 ...) or (1 4 ...), since it is clear that such elements exist
-- as products of those we have already found.
strongTerminals :: (Ord a) =>SearchTree [(a,a)] -> [Permutation a]
strongTerminals = instrongTerminals [] where
    instrongTerminals gs (T False xys ts) =
        case listToMaybe $ reverse $ filter (\(x,y) -> x /= y) xys of -- the first vertex that isn't fixed
        Nothing -> L.foldl' (\hs t -> instrongTerminals hs t) gs ts
        Just (x,y) -> if y `elem` (x .^^ gs)
            then gs
            else find1New gs ts
    instrongTerminals gs (T True xys []) = fromPairs xys : gs
    find1New gs (t:ts) = let hs = instrongTerminals gs t
        in if take 1 gs /= take 1 hs -- we know a new element would be placed at the front
            then hs
            else find1New gs ts
    find1New gs [] = gs

-- |Generate a SearchTree of graph automorphisms using distance partition
gAutsDPT ::forall a. (Ord a)=> Graph a -> SearchTree [(a,a)]
gAutsDPT g@(G vs' es') = dfs [] ([vs],[vs]) where
    dfs :: [(a,a)]->([[a]],[[a]])->SearchTree [(a,a)]
    dfs xys (srcPart,trgPart)
        --check compatibility at the final step
        | all isSingleton srcPart =
            let xys' = zip (concat srcPart) (concat trgPart)
            in T (isCompatible (xys++xys')) (xys++xys') []

        | otherwise = let (x:xs):srcCells = srcPart
                          yys   :trgCells = trgPart
                          srcPart' = intersectCells (xs : srcCells) (dps M.! x)
                       in T False xys -- the L.sort in the following line is so that we traverse vertices in natural order
                          [dfs ((x,y):xys) ((unzip . L.sort) (zip (filter (not . null) srcPart') (filter (not . null) trgPart')))
                          | (y,ys) <- picks yys,
                          let trgPart' = intersectCells (ys : trgCells) (dps M.! y),
                          map length srcPart' == map length trgPart']
    isCompatible xys = isAutomorphism g xys
    vs= S.toList vs'
    es = esfromhes es'
    dps = M.fromAscList [(v, distancePartitionS vs es v) | v <- vs]

{-Functions on permutations -}

-- |x .^ g returns the image of a vertex or point x under the action of the permutation g.
-- The dot is meant to be a mnemonic for point or vertex.
(.^) :: (Ord a) => a -> Permutation a -> a
x .^ P g = case M.lookup x g of
           Just y  -> y
           Nothing -> x -- if x `notElem` supp (P g), then x is not moved

-- |b -^ g returns the image of an edge or block b under the action of the permutation g.
-- The dash is meant to be a mnemonic for edge or line or block.
(-^) :: (Ord a) => S.Set a -> Permutation a -> S.Set a
xs -^ g = S.fromList [x .^ g | x <- S.toList xs]

-- |x .^^ gs returns the orbit of the point or vertex x under the action of the gs
(.^^) :: (Ord a) => a -> [Permutation a] -> [a]
x .^^ gs = orbit (.^) x gs

--a version of union which assumes the arguments are ascending sets (no repeated elements)
union:: Ord a => [a] -> [a] -> [a]
union (x:xs) (y:ys) =
    case compare x y of
    LT -> x : union xs (y:ys)
    EQ -> x : union xs ys
    GT -> y : union (x:xs) ys
union [] ys = ys
union xs [] = xs

-- the support of a permutation is the points it moves (returned in ascending order)
supp::Permutation a -> [a]
supp (P g) = M.keys g

minsupp :: Permutation c -> c
minsupp = head . supp

-- Semigroup to combine two permutations
instance Ord a => Semigroup (Permutation a) where
    g <> h = fromPairs [(x, x .^ g .^ h) | x <- union (supp g) (supp h)]

-- Add unity
instance Ord a =>Monoid (Permutation a) where
    mempty=P$ M.empty
    mappend = (<>)

--make a permutation from pairs (a point, its image under the permutation)
fromPairs :: Ord a => [(a, a)] -> Permutation a
fromPairs xys = P (M.fromList ( filter(uncurry(/=)) xys))

-- list the elts of the group, given a "transversal generating set"
eltsTGS :: Ord a => [Permutation a] -> [Permutation a]
eltsTGS tgs =
    let transversals = map (mempty:) $ L.groupBy (\g h -> minsupp g == minsupp h) tgs
    in map mconcat $ sequence transversals

closureS :: Ord a => [a] -> [a -> a] -> S.Set a
closureS xs fs = inclosure S.empty xs where
    inclosure interior (x:xs)
        | S.member x interior = inclosure interior xs
        | otherwise = inclosure (S.insert x interior) ([f x | f <- fs] ++ xs)
    inclosure interior [] = interior

closure :: Ord a => [a] -> [a -> a] -> [a]
closure xs fs = S.toList $ closureS xs fs 

orbit :: Ord a => (a -> t -> a) -> a -> [t] -> [a]
orbit action x gs = closure [x] [ (`action` g) | g <- gs]

--version of the Data.List function which assume that the lists are ascending sets (no repeated elements)
toListSet :: Ord b => [b] -> [b]
toListSet xs = map head $ L.group $ L.sort xs

-- recover a transversal generating set from a strong generating set
-- -- A strong generating set is a generating set gs such that <gs intersect si> = si
-- -- ie, its intersection with each successive stabiliser in the chain generates the stabiliser
tgsFromSgs :: Ord a => [Permutation a] -> [Permutation a]
tgsFromSgs sgs = concatMap transversal bs where
    bs = toListSet $ map minsupp sgs
    transversal b = closuretgs b $ filter ( (b <=) . minsupp) sgs
    closuretgs b gs = inclosuretgs M.empty (M.fromList [(b, mempty)]) where
        inclosuretgs interior boundary
            | M.null boundary = filter (/=mempty) $ M.elems interior
            | otherwise =
                let interior' = M.union interior boundary
                    boundary' = M.fromList [(x .^ g, h<>g) | (x,h) <- M.toList boundary, g <- gs] M.\\ interior'
                in inclosuretgs interior' boundary'

--construct edges from hyperedges
esfromhes:: (Ord a ,Eq a)=>S.Set (S.Set a) ->S.Set [a]
esfromhes = S.fromList. L.nub . concatMap generatePairs . S.toList
  where
    generatePairs set = [[x, y] | x <- list, y <- list, x < y]
      where
        list = S.toList set

{-Functions needed to calculate the strong generating set-}

distancePartitionS :: Ord a => [a] -> S.Set [a] -> a -> [[a]]
distancePartitionS vs eset v = distancePartition (S.singleton v) (S.delete v (S.fromList vs)) where
    distancePartition boundary exterior
        | S.null boundary = if S.null exterior then [] else [S.toList exterior] -- graph may not have been connected
        | otherwise = let (boundary', exterior') = S.partition (\v -> any (`S.member` eset) [L.sort [u,v] | u <- S.toList boundary]) exterior
                      in S.toList boundary : distancePartition boundary' exterior'

--check if an object is a singleton
isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False

intersectCells :: Ord a => [[a]] -> [[a]] -> [[a]]
intersectCells p1 p2 = concat [ [c1 `intersectAsc` c2 | c2 <- p2] | c1 <- p1]

-- |The (multi-)set intersection of two ascending lists. If both inputs are strictly increasing,
-- then the output is the set intersection and is strictly increasing. If both inputs are weakly increasing,
-- then the output is the multiset intersection (with multiplicity), and is weakly increasing.
intersectAsc :: Ord a => [a] -> [a] -> [a]
intersectAsc (x:xs) (y:ys) =
    case compare x y of
    LT -> intersectAsc xs (y:ys)
    EQ -> x : intersectAsc xs ys
    GT -> intersectAsc (x:xs) ys
intersectAsc _ _ = []

-- |Return all the ways to \"pick one and leave the others\" from a list
picks :: [a] -> [(a,[a])]
picks [] = []
picks (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- picks xs]

-- |Compatibility condition
isAutomorphism :: Ord a => Graph a -> [(a,a)]-> Bool
isAutomorphism g@(G vs es) pairs = ( es == S.fromList (map (-^ p) (S.toList es )))
    where
        p=fromPairs pairs

{-EXAMPLES-}

--function to initialize a graph from lists
graph :: (Ord t) => ([t], [[t]]) -> Graph t
graph (vs,es) = G (S.fromList vs) (S.fromList (map S.fromList es))

-- |c n is the cyclic graph on n vertices
c :: (Integral t) => t -> Graph t
c n | n >= 3 = graph (vs,es) where
    vs = [1..n]
    es = L.insert [1,n] [[i,i+1] | i <- [1..n-1]]
-- automorphism group   is D2n

c3 :: (Integral t) => t -> Graph t
c3 n | n >= 3 = graph (vs,es) where
    vs = [0..(n-1)]
    es = [[i,(i+1) `mod` n,(i+2) `mod` n] | i <- [0..(n-1)]]
