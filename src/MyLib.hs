{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists #-}

module MyLib
  ( orderSGS
  , eltsSGS
  , graphAuts
  , Graph (..)
  , Permutation (..)
  , symmetryGroup
  , CommutationMatrix (..)
  , mkCommutationMatrix
  , areCommuting
  , abelianDFS
  , FastPermutation (..)
  , toFastPermutations
  ) where

import Control.DeepSeq
import Data.Kind (Constraint, Type)
import Data.List (groupBy)
import Data.List qualified as L
import Data.Map qualified as M
import Data.Maybe
import Data.Ratio
import Data.Ord (comparing)
import Data.Set qualified as S
import Data.Vector (Vector)
import Data.Vector qualified as V
import Data.Vector.Generic ((!))
import Data.Vector.Unboxed qualified as U
import Debug.Trace (trace, traceShow)
import GHC.Generics

{-MAIN TYPES AND FUNCTIONS-}

-- | Definition of a (hyper)graph
data Graph a = G (S.Set a) (S.Set (S.Set a)) deriving (Eq, Ord, Show)

-- | Definition of a permutation
newtype Permutation a = P (M.Map a a)
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (NFData)

-- | Data structure organising the search of generating permutations
--  The boolean indicates whether or not this is a terminal / solution node
data SearchTree a = T Bool a [SearchTree a] deriving (Eq, Ord, Show, Functor)


-- | Data structures for group operations (needed for 1D representations)
class HasIdentity a where
  isIdentity :: a -> Bool

newtype GroupElement a = UnsafeGroupElement {unGroupElement :: Maybe a}
  deriving stock (Show, Eq, Ord)

instance HasIdentity (GroupElement a) where
  isIdentity = isNothing . unGroupElement

mkGroupLike :: (HasIdentity a) => a -> GroupElement a
mkGroupLike x
  | isIdentity x = UnsafeGroupElement Nothing
  | otherwise = UnsafeGroupElement (Just x)

instance (Semigroup a, HasIdentity a) => Semigroup (GroupElement a) where
  a <> b
    | isIdentity a = b
    | isIdentity b = a
    | otherwise = mkGroupLike $ fromJust (unGroupElement a) <> fromJust (unGroupElement b)

instance (Semigroup a, HasIdentity a) => Monoid (GroupElement a) where
  mempty = UnsafeGroupElement Nothing

type IsGroupElement :: Type -> Constraint
type IsGroupElement a = (Eq a, Ord a, HasIdentity a, Monoid a)


-- | Given a graph, return the strong generating set
graphAuts :: (Ord a) => Graph a -> [Permutation a]
graphAuts g = filter (/= mempty) (strongTerminals (gAutsDPT g))

-- | Given a strong generating set, return the order of the group it generates.
--  Note that the SGS is assumed to be relative to the natural order of the points on which the group acts.
orderSGS :: (Ord a) => [Permutation a] -> Integer
orderSGS sgs = product $ map (L.genericLength . fundamentalOrbit) bs
  where
    bs = toListSet $ map minsupp sgs
    fundamentalOrbit b = b .^^ filter ((b <=) . minsupp) sgs

-- | Given a strong generating set, return elements of the group it generates.
--  At first, we calculate transversal generating set and only then return elements of the group
eltsSGS :: (Ord a) => [Permutation a] -> [Permutation a]
eltsSGS sgs = eltsTGS (tgsFromSgs sgs)

-- | Return a strong generating set from the whole search tree.
--  For example, if we have already found (3 4), and then we find (1 2 3),
--  then there is no need to look for (1 3 ...) or (1 4 ...), since it is clear that such elements exist
--  as products of those we have already found.
strongTerminals :: (Ord a) => SearchTree [(a, a)] -> [Permutation a]
strongTerminals = instrongTerminals []
  where
    instrongTerminals gs (T False xys ts) =
      case listToMaybe $ reverse $ filter (\(x, y) -> x /= y) xys of -- the first vertex that isn't fixed
        Nothing -> L.foldl' (\hs t -> instrongTerminals hs t) gs ts
        Just (x, y) ->
          if y `elem` (x .^^ gs)
            then gs
            else find1New gs ts
    instrongTerminals gs (T True xys []) = fromPairs xys : gs
    find1New gs (t : ts) =
      let hs = instrongTerminals gs t
       in if take 1 gs /= take 1 hs -- we know a new element would be placed at the front
            then hs
            else find1New gs ts
    find1New gs [] = gs

-- | Generate a SearchTree of graph automorphisms using distance partition
gAutsDPT :: forall a. (Ord a) => Graph a -> SearchTree [(a, a)]
gAutsDPT g@(G vs' es') = dfs [] ([vs], [vs])
  where
    dfs :: [(a, a)] -> ([[a]], [[a]]) -> SearchTree [(a, a)]
    dfs xys (srcPart, trgPart)
      -- check compatibility at the final step
      | all isSingleton srcPart =
          let xys' = zip (concat srcPart) (concat trgPart)
           in T (isCompatible (xys ++ xys')) (xys ++ xys') []
      | otherwise =
          let (x : xs) : srcCells = srcPart
              yys : trgCells = trgPart
              srcPart' = intersectCells (xs : srcCells) (dps M.! x)
           in T
                False
                xys -- the L.sort in the following line is so that we traverse vertices in natural order
                [ dfs ((x, y) : xys) ((unzip . L.sort) (zip (filter (not . null) srcPart') (filter (not . null) trgPart')))
                | (y, ys) <- picks yys
                , let trgPart' = intersectCells (ys : trgCells) (dps M.! y)
                , map length srcPart' == map length trgPart'
                ]
    isCompatible xys = isAutomorphism g xys
    vs = S.toList vs'
    es = esfromhes es'
    dps = M.fromAscList [(v, distancePartitionS vs es v) | v <- vs]

{-PERMUTATIONS -}

-- | x .^ g returns the image of a vertex or point x under the action of the permutation g.
--  The dot is meant to be a mnemonic for point or vertex.
(.^) :: (Ord a) => a -> Permutation a -> a
x .^ P g = case M.lookup x g of
  Just y -> y
  Nothing -> x -- if x `notElem` supp (P g), then x is not moved

-- | b -^ g returns the image of an edge or block b under the action of the permutation g.
--  The dash is meant to be a mnemonic for edge or line or block.
(-^) :: (Ord a) => S.Set a -> Permutation a -> S.Set a
xs -^ g = S.fromList [x .^ g | x <- S.toList xs]

-- | x .^^ gs returns the orbit of the point or vertex x under the action of the gs
(.^^) :: (Ord a) => a -> [Permutation a] -> [a]
x .^^ gs = orbit (.^) x gs

-- a version of union which assumes the arguments are ascending sets (no repeated elements)
union :: (Ord a) => [a] -> [a] -> [a]
union (x : xs) (y : ys) =
  case compare x y of
    LT -> x : union xs (y : ys)
    EQ -> x : union xs ys
    GT -> y : union (x : xs) ys
union [] ys = ys
union xs [] = xs

-- the support of a permutation is the points it moves (returned in ascending order)
supp :: Permutation a -> [a]
supp (P g) = M.keys g

minsupp :: Permutation c -> c
minsupp = head . supp

-- Semigroup to combine two permutations
instance (Ord a) => Semigroup (Permutation a) where
  g <> h = fromPairs [(x, x .^ g .^ h) | x <- supp g `union` supp h]

-- Add unity
instance (Ord a) => Monoid (Permutation a) where
  mempty = P M.empty
  mappend = (<>)

-- make a permutation from pairs (a point, its image under the permutation)
fromPairs :: (Ord a) => [(a, a)] -> Permutation a
fromPairs xys = P (M.fromList (filter (uncurry (/=)) xys))

-- list the elements of the group, given a "transversal generating set"
eltsTGS :: (Ord a) => [Permutation a] -> [Permutation a]
eltsTGS tgs =
  let transversals = map (mempty :) $ L.groupBy (\g h -> minsupp g == minsupp h) tgs
   in map mconcat $ map reverse $ sequence transversals

closureS :: (Ord a) => [a] -> [a -> a] -> S.Set a
closureS xs fs = inclosure S.empty xs
  where
    inclosure interior (x : xs)
      | S.member x interior = inclosure interior xs
      | otherwise = inclosure (S.insert x interior) ([f x | f <- fs] ++ xs)
    inclosure interior [] = interior

closure :: (Ord a) => [a] -> [a -> a] -> [a]
closure xs fs = S.toList $ closureS xs fs

orbit :: (Ord a) => (a -> t -> a) -> a -> [t] -> [a]
orbit action x gs = closure [x] [(`action` g) | g <- gs]

-- version of the Data.List function which assume that the lists are ascending sets (no repeated elements)
toListSet :: (Ord b) => [b] -> [b]
toListSet xs = map head $ L.group $ L.sort xs

-- recover a transversal generating set from a strong generating set
-- -- A strong generating set is a generating set gs such that <gs intersect si> = si
-- -- i.e., its intersection with each successive stabiliser in the chain generates the stabiliser
tgsFromSgs :: (Ord a) => [Permutation a] -> [Permutation a]
tgsFromSgs sgs = concatMap transversal bs
  where
    bs = toListSet $ map minsupp sgs
    transversal b = closuretgs b $ filter ((b <=) . minsupp) sgs
    closuretgs b gs = inclosuretgs M.empty (M.fromList [(b, mempty)])
      where
        inclosuretgs interior boundary
          | M.null boundary = filter (/= mempty) $ M.elems interior
          | otherwise =
              let interior' = M.union interior boundary
                  boundary' = M.fromList [(x .^ g, h <> g) | (x, h) <- M.toList boundary, g <- gs] M.\\ interior'
               in inclosuretgs interior' boundary'

-- construct edges from hyperedges
esfromhes :: (Ord a, Eq a) => S.Set (S.Set a) -> S.Set [a]
esfromhes = S.fromList . L.nub . concatMap generatePairs . S.toList
  where
    generatePairs set = [[x, y] | x <- list, y <- list, x < y]
      where
        list = S.toList set

{-DISTANCE PARTITION-}

distancePartitionS :: (Ord a) => [a] -> S.Set [a] -> a -> [[a]]
distancePartitionS vs eset v = distancePartition (S.singleton v) (S.delete v (S.fromList vs))
  where
    distancePartition boundary exterior
      | S.null boundary = if S.null exterior then [] else [S.toList exterior] -- graph may not have been connected
      | otherwise =
          let (boundary', exterior') = S.partition (\v -> any (`S.member` eset) [L.sort [u, v] | u <- S.toList boundary]) exterior
           in S.toList boundary : distancePartition boundary' exterior'

-- check if an object is a singleton
isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton _ = False

intersectCells :: (Ord a) => [[a]] -> [[a]] -> [[a]]
intersectCells p1 p2 = concat [[c1 `intersectAsc` c2 | c2 <- p2] | c1 <- p1]

-- | The (multi-)set intersection of two ascending lists. If both inputs are strictly increasing,
--  then the output is the set intersection and is strictly increasing. If both inputs are weakly increasing,
--  then the output is the multiset intersection (with multiplicity), and is weakly increasing.
intersectAsc :: (Ord a) => [a] -> [a] -> [a]
intersectAsc (x : xs) (y : ys) =
  case compare x y of
    LT -> intersectAsc xs (y : ys)
    EQ -> x : intersectAsc xs ys
    GT -> intersectAsc (x : xs) ys
intersectAsc _ _ = []

-- | Return all the ways to \"pick one and leave the others\" from a list
picks :: [a] -> [(a, [a])]
picks [] = []
picks (x : xs) = (x, xs) : [(y, x : ys) | (y, ys) <- picks xs]

-- | Compatibility condition
isAutomorphism :: (Ord a) => Graph a -> [(a, a)] -> Bool
isAutomorphism g@(G vs es) pairs = (es == S.fromList (map (-^ p) (S.toList es)))
  where
    p = fromPairs pairs

{-ONE DIMENSIONAL REPRESENTATIONS-}

-- prime factorization
factorize :: Int -> Int -> [Int]
factorize _ 1 = []
factorize d n
  | d * d > n = [n]
  | n `mod` d == 0 = d : factorize d (n `div` d)
  | otherwise = factorize (d + 1) n

primeFactors :: Int -> [Int]
primeFactors = factorize 2

formatfactors :: [Int] -> [(Int, Int)]
formatfactors xs = recformat xs []
  where
    recformat [] fxs = fxs
    recformat xs fxs = recformat (filter (/= m) xs) [(m, length $ (filter (== m) xs))] ++ fxs
      where
        m = maximum xs

-- returns list of tuples (prime number, power in prime decomposition)
p_factors :: Int -> [(Int, Int)]
p_factors x = reverse $ formatfactors $ primeFactors x

-- calculate orders of group elements
element_orders :: IsGroupElement a => [a] -> [(a, (Int, Int))]
element_orders gs = [(g, head (p_factors $ order g)) | g <- gs, (length $ p_factors $ order g) == 1]
  where
    order g = 1 + (L.length $ takeWhile (/= g) $ tail $ iterate (<> g) g)

-- find generators with corresponding orbit length. it is needed for characters table.
-- here we use the structure theorem for finite abelian groups: they can be represented as a direct sum of cycles of prime power order
group_generators :: IsGroupElement a => [a] -> [(a, Int)]
group_generators gs = recgens ps_ini [] ord_gs [mempty]
  where
    ps_ini = p_factors $ length gs
    ord_gs = element_orders gs

    recgens [] gens cs_tail subgroup = simplify_order gens
    recgens ps gens cs_tail subgroup = recgens new_ps new_gens new_cs_tail new_subgroup
      where
        nice_cs = find_nice_cs cs_tail ps
        new_ps = update_pfactors ps nice_cs
        new_subgroup = update_subgroup subgroup nice_cs
        new_cs_tail = update_cs_tail new_subgroup new_ps cs_tail
        new_gens = [nice_cs] ++ gens

simplify_order :: IsGroupElement a => [(a,(Int, Int))]->[(a,Int)]
simplify_order gens = [(gen,p^ppower)| (gen,(p,ppower))<-gens]

update_pfactors :: IsGroupElement a => [(Int, Int)] -> (a, (Int, Int)) -> [(Int, Int)]
update_pfactors ((p,ppower):ps) (_, (nice_p, nice_power))
  | ppower - nice_power > 0 = (p, ppower - nice_power) : ps
  | ppower - nice_power == 0 = ps

update_cs_tail :: IsGroupElement a => [a] -> [(Int, Int)] -> [(a, (Int, Int))] -> [(a, (Int, Int))]
update_cs_tail new_subgroup new_ps cs_tail = [(fp, (p, ppower)) | (fp, (p, ppower)) <- cs_tail, fp `L.notElem` new_subgroup, (p, ppower) <= (L.maximum new_ps)]

update_subgroup :: IsGroupElement a => [a] -> (a, (Int, Int)) -> [a]
update_subgroup subgroup (nice_gen, (p, ppower)) = L.nub [h <> g | h <- subgroup, g <- powers_list]
  where
    powers_list = take (p ^ ppower) (iterate (<> nice_gen) mempty)

find_nice_cs :: IsGroupElement a => [(a, (Int, Int))] -> [(Int, Int)] -> (a, (Int, Int))
find_nice_cs cs_tail ps = L.maximumBy (comparing snd) (filter (\(x, (p, pk)) -> p == (fst pp) && pk <= (snd pp)) cs_tail)
  where
    pp = head ps

--type for abelianized group
newtype Coset = Coset (S.Set FastPermutation) deriving (Eq, Ord, Show)

instance HasIdentity Coset where
  isIdentity (Coset a) = unit_fp `L.elem` a where
    (FastPermutation v) = S.elemAt 0 a
    unit_fp= FastPermutation (U.generate (U.length v) id) 

instance Semigroup Coset where
  (Coset a) <> (Coset b) = Coset $ S.fromList [x<>y| x <- (S.toList a), y <- (S.toList b)]

-- build commutator subgroup [G,G]
commutator_subgroup :: [FastPermutation] -> [FastPermutation]
commutator_subgroup gs = L.nub [g <> h <> (invert g) <> (invert h) | g <- gs, h <- gs]

-- build abelianization G/[G,G]
abelianization_cs :: [FastPermutation] -> [Coset]
abelianization_cs gs = map Coset (L.nub [coset g cgs | g <- gs])
  where
    coset g cgs = S.fromList [g <> h | h <- cgs]
    cgs = commutator_subgroup gs

--abelianization for GroupElement instance
abelianization :: [FastPermutation] -> [GroupElement Coset]
abelianization g = map mkGroupLike (abelianization_cs g)

--G/[G,G] for a given graph
abfactorSymmetries :: (Ord t)=>Graph t ->[GroupElement Coset]
abfactorSymmetries g = abelianization $ fastsymmetryGroup g

--with given generators and character's index, return character
characters :: IsGroupElement a => [(a,Int)] -> Int -> [(a, Ratio Int)]
characters gens ind = [(g, frac_part $ (ind % 1)*phase )| (g, phase) <- gsphs] where
  gsphs = elementsandphases gens

--with given generators, return group elements with corresponding phases
elementsandphases :: IsGroupElement a => [(a,Int)]->[(a, Ratio Int)]
elementsandphases gens =  update_elphs [(mempty, 0 % 1)] gens where
  update_elphs elphs [] = elphs
  update_elphs elphs ((g,ord):gs) = update_elphs [((power g n) <> element, frac_part $ phase+n%ord ) | (element,phase) <-elphs, n<-[0..(ord-1)] ] gs

power :: IsGroupElement a => a -> Int -> a
power g n
  | n==0 = mempty
  | n > 0  = last $ take n (iterate (<> g) g)

frac_part :: Ratio Int -> Ratio Int
frac_part x = ((numerator x) `mod` (denominator x)) % (denominator x)  


{-MAXIMAL ABELIAN SUBGROUP-}

fastsymmetryGroup :: (Ord t) => Graph t -> [FastPermutation]
fastsymmetryGroup graph = V.toList $ toFastPermutations graph (V.fromList (symmetryGroup graph))

symmetryGroup :: (Ord t) => Graph t -> [Permutation t]
symmetryGroup = eltsSGS . graphAuts

-- maximal abelian subgroup as array of grouplike elements
abSymmetries :: (Ord t) => Graph t -> [GroupElement FastPermutation]
abSymmetries g = map mkGroupLike (abSymmetries_fps g)


data FastPermutation = FastPermutation (U.Vector Int) deriving (Eq, Ord, Show)

-- make fast permutations
toFastPermutations :: (Ord t) => Graph t -> Vector (Permutation t) -> Vector FastPermutation
toFastPermutations (G nodes _) = fmap magic
  where
    nodesList = S.toAscList nodes
    eltToIntMap = M.fromAscList $ zip nodesList [(0 :: Int) ..]
    eltToInt elt = let Just i = M.lookup elt eltToIntMap in i
    magic (P mapping) =
      FastPermutation . U.fromList $
        (\(elt, index) -> maybe index eltToInt (M.lookup elt mapping))
          <$> zip nodesList [0 ..]

instance HasIdentity FastPermutation where
  isIdentity (FastPermutation v) = v == U.generate (U.length v) id

instance Semigroup FastPermutation where
  (FastPermutation a) <> (FastPermutation b) = FastPermutation $ U.map (b !) a

-- find index of an integer
elemIndexInt :: U.Vector Int -> Int -> Int
elemIndexInt vx x = fromJust (U.elemIndex x vx)

-- make inverse
invert :: FastPermutation -> FastPermutation
invert (FastPermutation a) = FastPermutation $ U.generate (U.length a) (elemIndexInt a)

newtype CommutationMatrix = CommutationMatrix (Vector (Vector Bool))
  deriving stock (Show, Eq, Generic)
  deriving anyclass (NFData)

mkCommutationMatrix :: (Ord t) => Graph t -> Vector (Permutation t) -> CommutationMatrix
mkCommutationMatrix graph gs =
  CommutationMatrix $
    fmap (\g -> fmap (\h -> g <> h == h <> g) gs') gs'
  where
    gs' = toFastPermutations graph gs

areCommuting :: CommutationMatrix -> Int -> Int -> Bool
areCommuting (CommutationMatrix m) i j = m ! i ! j

data History = History
  { hIncluded :: !(Vector Int)
  , hMask :: !(Vector Bool)
  }
  deriving stock (Show, Eq)

abelianDFS :: (Ord t) => CommutationMatrix -> Vector (Permutation t) -> [History]
abelianDFS (CommutationMatrix comm) gs = go emptyHistory
  where
    emptyHistory :: History
    emptyHistory = History V.empty (V.replicate (V.length gs) True)
    addToHistory :: History -> Int -> History
    addToHistory (History included mask) i =
      History
        { hIncluded = included `V.snoc` i
        , hMask = V.zipWith (&&) mask (comm ! i)
        }
    getChoices :: History -> [Int]
    getChoices (History included mask) =
      V.toList . V.filter (not . flip S.member seen) . V.map fst . V.filter snd . V.indexed $ mask
      where
        seen = S.fromList . V.toList $ included

    mergeHistories :: [History] -> History
    mergeHistories hs = History included mask
      where
        included = V.fromList . S.toList . S.fromList $ concatMap (V.toList . hIncluded) hs
        mask = hMask . head $ hs

    go :: History -> [History]
    go history =
      case getChoices history of
        [] -> [history]
        cs ->
          let newHistories =
                L.sortOn (negate . V.length . hIncluded)
                  . fmap mergeHistories
                  . groupBy (\a b -> hMask a == hMask b)
                  . L.sortOn hMask
                  $ addToHistory history <$> cs
           in concatMap go newHistories

-- maximal abelian subgroup of graph automorphisms
abSymmetries_fps :: (Ord t) => Graph t -> [FastPermutation]
abSymmetries_fps gr = [gsfast ! index | index <- (V.toList int_form)]
  where
    gs = V.fromList $ symmetryGroup gr
    mkComm = mkCommutationMatrix gr gs
    branches = take 20 (abelianDFS mkComm gs)
    leaf = L.maximumBy (comparing (V.length . hIncluded)) branches
    int_form = hIncluded leaf
    gsfast = toFastPermutations gr gs

{-TEST FUNCTIONS-}
--abelian closure with given generators
ab_closure :: IsGroupElement a => [(a, (Int,Int))]->[a]
ab_closure gens = ab_closing [mempty] gens where
  ab_closing group [] = group
  ab_closing group (x:xs) = ab_closing (update_subgroup group x) xs

-- naive way to generate a group from a generating set
eltsbyclosure :: (Ord a) => [Permutation a] -> [Permutation a]
eltsbyclosure gs = closure [mempty] [(<> g) | g <- gs]

-- check that permutations are graph automorphisms
permutations_check :: (Ord a) => Graph a -> [Permutation a] -> Bool
permutations_check g@(G vs es) group = and [es == S.fromList (map (-^ p) (S.toList es)) | p <- group]

{-EXAMPLES-}

-- function to initialize a graph from lists
graph :: (Ord t) => ([t], [[t]]) -> Graph t
graph (vs, es) = G (S.fromList vs) (S.fromList (map S.fromList es))

-- | c n is the cyclic graph on n vertices
c :: (Integral t) => t -> Graph t
c n | n >= 3 = graph (vs, es)
  where
    vs = [1 .. n]
    es = L.insert [1, n] [[i, i + 1] | i <- [1 .. n - 1]]

-- rectangle lattice
rect :: (Integral t) => t -> t -> Graph t
rect n k = graph (vs, es)
  where
    vs = [0 .. n * k - 1]
    es = [[k * i + j, k * i + ((j + 1) `mod` k)] | i <- [0 .. n - 1], j <- [0 .. k - 1]] ++ [[k * i + j, k * ((i + 1) `mod` n) + j] | i <- [0 .. n - 1], j <- [0 .. k - 1]]

-- cyclic hypergraph with 3-vertex edges
c3 :: (Integral t) => t -> Graph t
c3 n | n >= 3 = graph (vs, es)
  where
    vs = [0 .. (n - 1)]
    es = [[i, (i + 1) `mod` n, (i + 2) `mod` n] | i <- [0 .. (n - 1)]]
