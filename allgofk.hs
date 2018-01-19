--contains implementations of algorithms for finding g_r(k), the r-th highest
--number writable with k ones using addition and multiplication, both concretely
--and abstractly; see accompanying paper for details and proof
--I make no claim about the efficiency or quality of this code, only its
--correctness.
--NOTE that attempting to run the concrete version with r larger than the number
--of distinct values that can be made with k ones, will result in an error in
--highlight (it will call head on an empty list).

--The three algorithms from the paper differ only in their main loop and answer
--extraction; the underlying machinery is mostly the same
module Main where
import Ratio
import List
import System.IO
import System.Environment

--SECTION 0: GENERAL UTILITIES NOT REQUIRING SPECIAL DATA TYPES

--ktobeat: takes a floating point value x and returns the smallest k such that
--g(k)>=x
--not actually used in this program
ktobeat :: (RealFloat a) => a -> Integer
ktobeat x = (max 1 . minimum)[ceiling(3 * (logBase 3 .fromIntegral. ceiling) x),
	2 + ceiling(3 * logBase 3 (fromIntegral (ceiling x) / 2)),
	4 + ceiling(3 * logBase 3 (fromIntegral (ceiling x) / 4))]

--subsets: takes an integer n and a list l, and returns a list of pairs (S,T),
--where the S's are all the size-n subsets of l (the same element appearing
--multiple times in l is considered as multiple distinct elements), and the T's
--are their complements
subsets :: Integer -> [a] -> [([a],[a])]
subsets 0 l = [([],l)]
subsets _ [] = []
subsets n (x:xs) = map2 (x:) (subsets n xs) ++ map1 (x:) (subsets (n-1) xs)

--subsetsle: same as subsets, except subsets have <=n elements instead of
--exactly n
subsetsle :: Integer -> [a] -> [([a],[a])]
subsetsle 0 l = [([],l)]
subsetsle _ [] = [([],[])]
subsetsle n (x:xs)=map2 (x:) (subsetsle n xs) ++ map1 (x:) (subsetsle (n-1) xs)

--map1 and map2: given a function and a list of pairs, map that function over
--all the 1st elts of the pairs, all the 2nd elts of the pairs, respectively
map1 :: (a -> b) -> [(a,c)] -> [(b,c)]
map2 :: (a -> b) -> [(c,a)] -> [(c,b)]

map1 f l = let m = unzip l in zip (map f (fst m)) (snd m)
map2 f l = let m = unzip l in zip (fst m) (map f (snd m))

--pairfilter: given a predicate and a list of pairs, filter that list according
--to whether or not both elements of the pair satisfy the predicate
pairfilter :: (a -> Bool) -> [(a,a)] -> [(a,a)] --yeah, uncurried, kind of
pairfilter p = filter (p . fst) . filter (p . snd)

--maponce: given a function f and a list l, returns a list of lists l', where
--each l' is the same as l, except that one of its elements has had f applied to
--it
--not actually used in this program
maponce :: (a -> a) -> [a] -> [[a]]
maponce f [] = []
maponce f (x:xs) = ((f x:xs):map (x:) (maponce f xs))

--concatMaponce: given a function f w/list output and a list l, returns a list
--of lists l', where each l' is the same as l, except that one of its elements
--has had f applied to it and the result spliced into the list at that position
--NOTE: the analogy concatMaponce : maponce :: concatMap : map is, I think,
--suggestive, but it's pretty loose; in particular concatMaponce is not equal to
--concat . maponce
concatMaponce :: (a -> [a]) -> [a] -> [[a]]
concatMaponce f [] = []
concatMaponce f (x:xs) = map (:xs) (f x) ++ map (x:) (concatMaponce f xs)

--winf: takes a binary function f and two Maybes; if both Maybes are valid, does
--the function; if only one is, returns that one; if neither is, return nothing
winf :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
winf f Nothing x = x
winf f x Nothing = x
winf f (Just a) (Just b) = Just (f a b)

--l2ml: Given a function and a list of Maybes, strips out the Nothings, then
--applies the function (returned as a Just); unless the resulting list is null,
--in which case Nothing is returned
l2ml :: ([a] -> b) -> [Maybe a] -> Maybe b
l2ml f l = let m = [a | Just a <- l] in if null m then Nothing else Just (f m)

--sortedpartition: Takes a list and a function, and splits the list into the
--fibers of that function (generalizing partition from the standard library)...
--however, for simplicity, and because it's all we need here, we'll assume that
--there's a total order on the image space of the function, and the list has
--already been sorted with respect to this
sortedpartition :: (Eq b) => (a -> b) -> [a] -> [[a]]
sortedpartition f [] = []
sortedpartition f [x] = [[x]]
sortedpartition f (x:y:xs) =
	let p=sortedpartition f (y:xs) in
		if f x == f y then (x:head p):tail p
		else [x]:p

--SECTION 1: DATA TYPES AND UTILITIES FOR THEM

data (RealFrac a) => Affine a  = a `Xplus` a deriving (Eq, Ord)
--Affine a: Affine functions in a
--a `Xplus` b represents ax+b
--Note Ord is derived; the result is that comparisons are made by which is
--eventually greater

instance (RealFrac a) => Show (Affine a) where
	show (a `Xplus` b) = show a ++ "x+" ++ show b
--a `Xplus` b is displayed as ax+b

--plus: adds two affines
plus :: (RealFrac a) => Affine a -> Affine a -> Affine a
(a `Xplus` b) `plus` (c `Xplus` d) = (a+c) `Xplus` (b+d)

--multiplies two affines; returns error if both nonconstant
times :: (RealFrac a) => Affine a -> Affine a -> Affine a
(a `Xplus` b) `times` (0 `Xplus` k) = (k*a) `Xplus` (k*b)
(0 `Xplus` k) `times` (c `Xplus` d) = (k*c) `Xplus` (k*d)
times _ _ = error "Can't multiply two affines"

--multiplies an affine by a scalar
sctimes :: (RealFrac a) => Affine a -> a -> Affine a
(a `Xplus` b) `sctimes` k = (k*a) `Xplus` (k*b)

--divides an affine by a scalar
scdiv :: (RealFrac a) => Affine a -> a -> Affine a
a `scdiv` k = a `sctimes` recip k

--takes an affine rational that is actually just an integer, and returns it as
--an actual integer; otherwise, error
aff2int :: Affine Rational -> Integer
aff2int (a `Xplus` b) = if a==0 && denominator b == 1 then numerator b else
	error "aff2int: Not an integer"

--equalat: given two affines, returns their point of intersection, or 1 if
--they're parallel; the idea is that past the returned point, whichever function
--is eventually greater, is actually greater
--no longer used
equalat :: (RealFrac a) => Affine a -> Affine a -> a
equalat (a `Xplus` b) (c `Xplus` d) = if a/=c then (d-b)/(a-c) else 1

--APTTree: Abstract Plus-Times tree
--In the paper, these are called abstract +,*,1-expressions
--Obviously, they are represented here as trees
data APTTree = LTimes [APTTree] --a product, of arbitrarily many subexpressions;
				--should not be empty, as in this context, empty
				--products don't make sense
	| Clump3 Integer --Clump3 n represents a clump of 3s that is missing n
			 --threes; in the paper, these are denoted 3^(Z-n)
			 --These will *only* occur inside products; a standalone
			 --clump would be LTimes [Clump3 n] rather than just
			 --Clump3 n (this is the only case where we'd use a
			 --singleton product - as it's not really a singleton at
			 --all)
	| PlusOne APTTree -- PlusOne A denotes A+1
	| OneLeaf --the number 1
	| Plus APTTree APTTree -- Plus A B denotes A+B
	deriving (Eq, Ord) --deriving Ord??  Yes, Ord is derived; this means
	--that comparison of APTTrees has nothing to do with their actual value;
	--there are other functions for doing that.  The purpose of deriving Ord
	--is for the function canonpermute.  Canonpermute takes an APTTree and
	--returns a canonical form for it; this involves sorting children wrt
	--their derived order.  NOTE: DO NOT change the derived order without
	--making appropriate modifications to canonpermute!  Canonpermute makes
	--several assumptions about the derived order, and will not work without
	--modifications if those assumptions are violated!

--twoLeaf and threeLeaf: [2] and [3], respectively
twoLeaf :: APTTree
twoLeaf = PlusOne OneLeaf
threeLeaf :: APTTree
threeLeaf = PlusOne twoLeaf

--constLeaf: constLeaf n returns what is in the paper called [n]
--constLeaf 2 and constLeaf 3 get special names, seen above
constLeaf :: Integer -> APTTree
constLeaf 1 = OneLeaf
constLeaf n = PlusOne (constLeaf (n-1))

--a function for showing APTTrees nicely; this is new as of this implementation;
--previously Show was derived, which was awful to parse.  I don't know why I
--didn't do this earlier.
instance Show APTTree where
	show OneLeaf = "1"
	show (Plus a b) = show a ++ "+" ++ show b
	show (PlusOne a) = "1+" ++ show a
	show (Clump3 n) | n==0	= "3^Z"
		        | n>0	= "3^(Z-" ++ show n ++ ")"
		        | n<0	= "3^(Z+" ++ show (-n) ++ ")"
	show (LTimes l) = (concat . intersperse "*" .
			 map ("("++) . map (++")") . map show) l

--val: computes the value of an APTTree, UNDER the assumption that k is 0 mod 3!
--if k is *not* 0 mod 3, you'll have to adjust the linear term afterward
--(fortunately, this does not affect comparison)
val :: APTTree -> Affine Rational
val (Plus a b) = val a `plus` val b
val (PlusOne a) = (0 `Xplus` 1) `plus` val a
val (LTimes a) = foldl times (0 `Xplus` 1) (map val a)
val OneLeaf = 0 `Xplus` 1
val (Clump3 n) = (3^^(-n)) `Xplus` 0


--cmpval: compares APTTrees by value
cmpval :: APTTree -> APTTree -> Ordering
cmpval a b = compare (val a) (val b)

--backwards: reverses an ordering
backwards :: Ordering -> Ordering
backwards LT = GT
backwards GT = LT
backwards EQ = EQ

--reverse cmpval
rcmpval :: APTTree -> APTTree -> Ordering
rcmpval a b = backwards (cmpval a b)

--threes: returns the number of threes needed for a given APTTree
--FIX for new canonpermute
threes :: APTTree -> Integer
threes a = zeroneg (threes1 a) --threes1 determines the actual number of threes;
				--if it's negative, we return 0 instead

--zeroneg: zeroes a negative number, identity otherwise
zeroneg :: (Real a) => a -> a
zeroneg n = if n < 0 then 0 else n

--threes1: helper function for threes
threes1 :: APTTree -> Integer
threes1 (LTimes [Clump3 n]) = n+1 --a clump standing alone requires n+1 threes,
			--not n, as described in the paper
threes1 a = threes2 a	--otherwise, we call the recursive helper function,
			--threes2

--threes2: helper function for threes
threes2 :: APTTree -> Integer
--note that Plus and PlusOne call threes1, while LTimes calls threes2; why's
--this? because if a clump occurs in an additive context, it needs an additional
--three, while it doesn't in a multiplicative context
threes2 (Plus a b) = threes1 a + threes1 b
threes2 (PlusOne a) = threes1 a
threes2 (LTimes a) = sum (map threes2 a)
threes2 OneLeaf = 0
threes2 (Clump3 n) = n

--canonpermute: Produces a "canonical form" for a given APTTree; see NOTE above
--regarding the derived order on the APTTree datatype
--has a helper function, gpthrees
canonpermute :: APTTree -> APTTree
--put summands in canonical order
canonpermute (Plus a b) =
	let	pa=canonpermute a
		pb=canonpermute b
	in Plus (min pa pb) (max pa pb)
canonpermute (PlusOne a) = PlusOne (canonpermute a)
--simplify products of 1 element
canonpermute (LTimes [Clump3 n]) = LTimes [Clump3 n]
--note that if the only thing in our product is a clump, we do not get rid of
--the product!  A clump hardly makes sense outside of a product.
canonpermute (LTimes [a]) = canonpermute a
--NOTE the following line makes the assumption that LTimes is first in the
--derived order!
--collapse multiple layers of product
canonpermute (LTimes ((LTimes l):ts)) = (canonpermute . LTimes) (l++ts)
--if there's a product among l's factors, first sort, then call canonpermute
--again, so above line will be invoked; otherwise, recurse and group threes
canonpermute (LTimes l)
	| any isprod l = (canonpermute . LTimes . sort) l
	| otherwise = (LTimes . sort . gpthrees . sort . map canonpermute) l
canonpermute OneLeaf = OneLeaf
canonpermute (Clump3 n) = Clump3 n

--gpthrees: given a list of factors for an LTimes, to which (sort . map
--canonpermute) has already been applied, groups any free threeLeafs into a
--clump if both exist
--NOTE this function assumes that Clump3 precedes threeLeaf in the derived
--order!
--NOTE this function does not necessarily preserve sortedness!
gpthrees :: [APTTree] -> [APTTree]
gpthrees [] = []
gpthrees (Clump3 m:PlusOne(PlusOne OneLeaf):ts) = Clump3 (m-1):gpthrees ts
gpthrees (Clump3 m:t:ts) = t:gpthrees (Clump3 m:ts)
gpthrees (t:ts) = t:gpthrees ts

--isprod: is it a product?
isprod :: APTTree -> Bool
isprod (LTimes _) = True
isprod _ = False

--isclump: is it a clump?
isclump :: APTTree -> Bool
isclump (Clump3 _) = True
isclump _ = False

--canonub: since we will often be dealing with lists of APTTrees, it is useful
--to have a "canonical form" for those too... though these are unsorted, so it's
--not really canonical
canonub :: [APTTree] -> [APTTree]
canonub = nub . map canonpermute

--ltmap: Given a function f:[APTTree]->[APTTree] and a list of APTTrees which
--are assumed to be of the form LTimes m, return the list of LTimes (f m).
--Anything not a product will be discarded
ltmap :: ([APTTree] -> [APTTree]) -> [APTTree] -> [APTTree]
ltmap f l = [LTimes (f m) | LTimes m <- l]

--nonclumps: Given a list of APTTrees, counts the number of them that are not
--clumps
nonclumps :: [APTTree] -> Integer
nonclumps = genericLength . filter (not . isclump)

--tsubsets: See subsets and subsetsle above.  However, this function only works
--on lists of APTTrees.  If the number input is n, it returns subsets that
--either: 1. are of size exactly n or 2. are of size at most n, and include at
--least one clump.  Conceptually, it returns subsets of size exactly n, where a
--clump is a wildcard in terms of size.  NOTE that, as with subsets and
--subsetsle, the selected sets are returned as the first element of each pair,
--not the second!  This is consistent with subsets and subsetsle, of course, but
--when we compute beta^-1, we're going to want to reverse this at some point.
tsubsets :: Integer -> [APTTree] -> [([APTTree],[APTTree])]
tsubsets 0 l = [([],l)]
tsubsets _ [] = []
tsubsets n(x@(Clump3 _):xs)=map2(x:)(tsubsets n xs)++map1(x:)(subsetsle (n-1)xs)
tsubsets n (x:xs) = map2 (x:) (tsubsets n xs) ++ map1 (x:) (tsubsets (n-1) xs)

data Mod3 = ZeroM3 | OneM3 | TwoM3 deriving (Eq, Show)
--yes, an enumerated type for congruence classes mod 3.  Probably totally
--unnecessary, but included anyway

--unmod3: canonical integer representation of a congruence class mod 3
unmod3 :: Mod3 -> Integer
unmod3 ZeroM3 = 0
unmod3 OneM3 = 1
unmod3 TwoM3 = 2

--mod3: converts an integer to a Mod3
mod3 :: Integer -> Mod3
mod3 n | n `mod` 3==0 = ZeroM3
       | n `mod` 3==1 = OneM3
       | n `mod` 3==2 = TwoM3

--the Num class may seem a poor fit for the Mod3 type - abs and signum don't
--actually make any sense - but the reason this declaration is that fromInteger
--instance; this lets you just type, say, '0' at an interpreter rather than
--"ZeroM3" all the time
instance Num Mod3 where
	fromInteger = mod3
	a + b = mod3 (unmod3 a + unmod3 b)
	a * b = mod3 (unmod3 a * unmod3 b)
	a - b = mod3 (unmod3 a - unmod3 b)
	negate = mod3 . negate . unmod3
	abs = const OneM3
	signum = const ZeroM3

--valadjust: for adjusting values, as described in the comment for val; takes an
--affine and a scalar, and divides the linear term of the affine by the scalar
valadjust :: (RealFrac a) => a -> Affine a -> Affine a
valadjust k (a `Xplus` b) = (a/k) `Xplus` b

--g1adjust: the multiplicative adjustment corresponding to a given mod3 value;
--primarily intended for providing a second argument to valadjust (and returns
--Rational for that reason)
g1adjust :: Mod3 -> Rational
g1adjust ZeroM3 = 1
g1adjust TwoM3 = 2
g1adjust OneM3 = 4

--plusalso: the additive adjustment corresponding to a given mod3 value;
plusalso :: Mod3 -> Integer
plusalso ZeroM3 = 0
plusalso TwoM3 = 2
plusalso OneM3 = 4

--relval: returns the actual value of an APTTree; takes a Mod3 k and an APTTree,
--and returns the value of the APTTree, assuming it's a k-APTTree
relval :: Mod3 -> APTTree -> Affine Rational
relval k t = valadjust (g1adjust k) (val t)

data TransType = Alpha | Beta | Gamma | Delta deriving (Eq, Ord, Show)
--TransType, for "transformation type"; represents the four types of
--transformations in the paper.  Actually, it represents their inverses.  Notice
--the derivation of Ord; Alpha<...<Delta.  So when expanding on a node, we will
--only apply transformations less than or equal to the one that got us there.

--TreeTree: the big one.  This data type represents a tree of APTTrees, a
--subtree of the abstract g(k)-tree.
--In order, its fields are:
--1. Bool picked? - Has this node been marked for expansion?
--2. [TreeTree] children - this node's children
--3. Bool dcpop - has this node had its delta^-1 and gamma^-1 children, as well
--as top-level type 0 alpha^-1 children if it's not a product, computed?
--4. Bool a0pop - has this node had all its type 0 alpha^-1 children computed?
--5. Integer beta# - the next stage of beta^-1 children to generate
--6. Integer alpha# - the next stage of alpha^-1 children to generate
--7. Integer ab-level - If this node was generated by beta^-1 or non-type-0
--alpha^-1, at what stage?  Otherwise, it's 0
--8. Transtype state - By what inverse transformation was this node generated?
--For the starting node, this is set to Delta
--9. APTTree content - what expression does this node represent?
data TreeTree=TT Bool [TreeTree] Bool Bool Integer Integer Integer TransType
	--    picked? children  dcpop a0pop beta#  alpha# ab-level    state
	APTTree
	--content
	deriving (Show, Eq)
--I don't remember why this thing derives Eq.  It derives Show for debugging
--purposes.  If you want it to look nice but only want the numerical
--information, run the function tt2m1 in "answer extraction", and then show the
--result of that

--newabTT: given a stage, a TransType and an APTTree, makes a new TreeTree with
--that information and all the default settings
newabTT :: Integer -> TransType -> APTTree -> TreeTree
newabTT = TT False [] False False 2 1

--newTT: given a TransType and an APTTree, makes a new TreeTree with that
--information and all the default settings
newTT :: TransType -> APTTree -> TreeTree
newTT = newabTT 0

--st: returns the state of a TreeTree
st :: TreeTree -> TransType
st (TT _ _ _ _ _ _ _ state _) = state

--ls: returns whether or not a TreeTree is marked
ls :: TreeTree -> Bool
ls (TT onlist _ _ _ _ _ _ _ _) = onlist

--tr: returns the content of a TreeTree
tr :: TreeTree -> APTTree
tr (TT _ _ _ _ _ _ _ _ tree) = tree

--ch: returns the children of a TreeTree
ch :: TreeTree -> [TreeTree]
ch (TT _ kids _ _ _ _ _ _ _) = kids

--lev: returns the stage of a TreeTree
lev :: TreeTree -> Integer
lev (TT _ _ _ _ _ _ lv _ _) = lv

--cmpTval: like cmpval, but for TreeTrees
cmpTval :: TreeTree -> TreeTree -> Ordering
cmpTval a b = compare (val (tr a)) (val (tr b))

--rcmpTval: reverse cmpTval
rcmpTval :: TreeTree -> TreeTree -> Ordering
rcmpTval a b = backwards (cmpTval a b)

--a generic tree type, for which I will write a function for
--pretty-printing
data MTree a = M1 a [MTree a]

--given an MTree, is it a leaf?
nonleaf :: MTree a -> Bool
nonleaf (M1 a l) = not (null l)

--stripleaves: removes the leaves from a tree
--if given a leaf, doesn't function sensibly :P
stripleaves :: MTree a -> MTree a
stripleaves (M1 x []) = error "Can't stripleaves a leaf"
stripleaves (M1 x l) = M1 x ((map stripleaves . filter nonleaf) l)

instance (Show a) => Show (MTree a) where
	show (M1 a l) = show a ++ "\n" ++ --first, print out a
		(unlines . map indent1 . lines . concatMap show) l
		--then, print out the children, indented

--indent a string by 1 while turning groups of 8 spaces into tabs
indent1 :: String -> String
indent1 (' ':' ':' ':' ':' ':' ':' ':s)='\t':s
indent1 ('\t':s)='\t':indent1 s
indent1 s=' ':s

--SECTION 2: THE MAIN LOOP: STARTING, MARKING, AND TERMINATING

--g1tree: given a congruence class mod 3, returns the appropriate starting
--expression for that congruence class
g1tree :: Mod3 -> APTTree
g1tree ZeroM3 = LTimes [Clump3 0]
g1tree TwoM3 = LTimes [Clump3 0, twoLeaf]
g1tree OneM3 = LTimes [Clump3 0, twoLeaf, twoLeaf]

--initTT: Returns the starting TreeTree for the given congruence class
initTT :: Mod3 -> TreeTree
initTT a = newTT Delta (g1tree a)

--gtree: given a k, returns the expression for g(k) - for those who want to run
--the concrete algorithm
cgtree :: Integer -> APTTree
cgtree k | k==1	  	   = OneLeaf
	 | k `mod` 3 == 0  = LTimes (genericReplicate (k `div` 3) threeLeaf)
	 | k `mod` 3 == 2  = LTimes ((genericReplicate (k `div` 3) threeLeaf) ++
				[twoLeaf])
	 | k `mod` 3 == 1  = LTimes((genericReplicate ((k `div` 3)-1) threeLeaf)
				++ [twoLeaf,twoLeaf])

--cinitTT: Concrete analog to initTT
cinitTT :: Integer -> TreeTree
cinitTT a = newTT Delta (cgtree a)

--finalTT: The main loop for the abstracted algorithm.  Takes an r and a
--congruence class mod 3, and returns the final tree.  We take the initial tree
--(initTT a), mark the appropriate nodes (highlight), and then repeatedly expand
--marked nodes (nexttree) and then mark nodes (highlight) until we've found r+1
--distinct values (found (r+1)).  Why r+1?  Because this makes sure we have all
--the ways of making the rth, allowing us to check the minimum # of 3s needed to
--make any of them.
finalTT :: Integer -> Mod3 -> TreeTree
finalTT r a = until (found (r+1)) (highlight . nexttree) (highlight (initTT a))

--cfinalTT: The concrete version of above.  It's the same, except it takes an
--integer k instead of just a congruence class mod 3, use the concrete starting
--tree cinitTT a, and we stop once we've found r, as we don't need to compute
--number of threes afterward - we can just find the rth value and stop.
cfinalTT :: Integer -> Integer -> TreeTree
cfinalTT r a = until (found r) (highlight . nexttree) (highlight (cinitTT a))

--thoroughTT: The main loop, for the third variation of our algorithm, the one
--that lets us determine h_kr and T_kr in general.  Again, we start with (initTT
--a), but now highlight is replaced with (rmark a), which will mark all nodes of
--value greater than (lambda_a)x.  Also, nexttree is replaced with nextftree,
--which is like nexttree except its version of beta^-1 won't generate things in
--the listed infinite families.  Finally, instead of checking how many values
--we've found, we start when after marking, we find that no leaves are marked,
--i.e., there's nothing to expand.  Note that no leaves being marked implies
--there's nothing to expand, as if there were something to expand, something
--would have to have been marked that hadn't been marked previously, meaning it
--would be a leaf as it couldn't have been expanded.
thoroughTT :: Mod3 -> TreeTree
thoroughTT a = until leavesunmarked (rmark a . nextftree) (rmark a (initTT a))

--highlight: highlights appropriate nodes recursively.  If not highlighted,
--highlights it.  If highlighted, finds the kid with the highest unmarked
--descendant, and recurses on that.  NOTE that this permutes the list of
--children.
highlight :: TreeTree -> TreeTree
highlight (TT False kids dc a0 b a lv state tree)=
	TT True kids dc a0 b a lv state tree
highlight (TT True kids dc a0 b a lv state tree) =
	let (exhkids,kids2)=partition (null . nonpicklist) kids
--exhkids: children with all descendants already picked
--kids2: those with not all descendants already picked
	    l=sortBy rhnpcmp kids2 in
		if null l then error "Not enough possible values" else
		TT True (highlight (head l):(tail l++exhkids))
			dc a0 b a lv state tree

--hnp: returns the (content of the) highest unmarked descendant
hnp :: TreeTree -> APTTree
hnp = maximumBy cmpval . nonpicklist

--hnpcmp: compare TreeTrees by the value of their highest unmarked descendant
hnpcmp :: TreeTree -> TreeTree -> Ordering
hnpcmp a b = cmpval (hnp a) (hnp b)

--rhncpcmp: reverse hnpcmp
rhnpcmp :: TreeTree -> TreeTree -> Ordering
rhnpcmp a b = backwards (hnpcmp a b)

--picklist: list of (contents of) highlighted nodes of the tree - not sorted or
--nubbed or anything
picklist :: TreeTree -> [APTTree]
picklist (TT lst kids _ _ _ _ _ _ tree) = (if lst then [tree] else []) ++
	concatMap picklist kids

--nonpicklist: See picklist, instead uses non-highlighted nodes
nonpicklist :: TreeTree -> [APTTree]
nonpicklist (TT lst kids _  _ _ _ _ _ tree) =(if not lst then [tree] else []) ++
	concatMap nonpicklist kids

--alllist: See picklist, but uses all nodes
alllist :: TreeTree -> [APTTree]
alllist (TT _ kids _ _ _ _ _ _ tree) = tree:(concatMap alllist kids)

--rmark: Recursively marks all nodes with value greater than (lambda_m)x.
rmark :: Mod3 -> TreeTree -> TreeTree
rmark m (TT _ kids dc a0 b a lv state tree) =
	TT (relval m tree > limitval m)
	(map (rmark m) kids) dc a0 b a lv state tree

--limitval: takes k, returns (lambda_k)x
limitval :: Mod3 -> Affine Rational
limitval ZeroM3 = (2%3) `Xplus` (0%1)
limitval TwoM3 = (2%3) `Xplus` (0%1)
limitval OneM3 = (3%4) `Xplus` (0%1)

--found: Given an integer r and a TreeTree, checks whether or not at least r
--different values have been marked in that TreeTree
found :: Integer -> TreeTree -> Bool
found r t = (genericLength . nub . (map val) . picklist) t >= r

--leavesunmarked: returns true if all leaves are unmarked
leavesunmarked :: TreeTree -> Bool
leavesunmarked tt = ((not . null . ch) tt || (not . ls) tt) &&
	all leavesunmarked (ch tt)

--SECTION 3: THE MAIN LOOP: THE NEXTTREE FUNCTION

--nexttree: Expands upon marked nodes
nexttree :: TreeTree -> TreeTree
nexttree tt@(TT False _ _ _ _ _ _ _ _) = tt
--If a node is unmarked, leave it alone.  Otherwise...
nexttree tt@(TT True kids dc a0 b a lv state tree) =
	let dgo = state == Delta
	    --dgo: should this node have delta^-1 children? (at all)
	    cgo = state >= Gamma
	    --cgo: how about gamma?
	    bgo = state >= Beta
	    --bgo: how about beta? (alpha is automatic)
	    bkids = filter (\x -> st x==Beta && lev x == b-1) kids
	    --bkids: list of children generated by beta^-1 of previous level -
	    --when one of these is marked, or if there are none, it's time to
	    --start generating beta^-1s of the current level
	    akids = filter (\x -> st x==Alpha && lev x == a-1) kids
	    --akids: same thing for alpha^-1.  Unlike with beta, however, with
	    --alpha we have the additional complication that we don't use alpha
	    --at all until the beta stage has passed the minimum length of a
	    --product.  (Barring the use of type-0 alphas when the expression
	    --itself is not a product.)
	    bexh = maybe False (<b) (minlength tree)
	    --bexh: Has the stage passed the minimum length of a product?  Note
	    --that minlength returns a Maybe Integer; Nothing indicates
	    --infinity, i.e. no products without clumps, in which case we'll
	    --consider that a no
	    bgone = bgo && (null bkids || any ls bkids)
	    --bgone: Do we actually go ahead with beta^-1?  This requires both
	    --the appropriate state (bgo), and a kid of the previous stage to be
	    --marked (or for there to be no kids of the previous stage).
	    agone = bexh && (null akids || any ls akids)
	    --agone: Do we actually go ahead with alpha^-1?  This requires both
	    --it being time for alpha at all (bexh), and the condition on the
	    --children as with beta.
	    bint = if bgone then 1 else 0
	    --bint: bgone converted to an integer
	    aint = if agone then 1 else 0 in
	    --aint: agone converted to an integer
		TT True (map nexttree kids ++
		--True: the node remains marked
		--map nexttree kids: let's recursively expand on the (marked)
		--children
		-- ++: ...and add some new children, seeing as that's what this
		-- function does.  The second argument to that ++ will form the
		-- bulk of this function.
		(if not dc && dgo then
		--if delta & gamma haven't been generated yet, and delta is
		--applicable
		maybe [] ((:[]) . (newTT Delta)) (delta tree) else []) ++
		--then throw in delta
		(if not dc && cgo then
		--if delta & gamma haven't been generated yet, and gamma is
		--applicable
		(map (newTT Gamma) . canonub . gamma) tree else []) ++
		--then throw in gamma
		(if bgone then
		--if it's time to generate the next level of beta^-1
		(map (newabTT b Beta) . canonub . nextb b) tree else []) ++
		--then do just that
		(if not dc && not (isprod tree) then
		--if delta & gamma haven't been generated yet, and the
		--expression is not a product
		(map (newTT Alpha) . canonub . mnexta0) tree else []) ++
		--then generate those top-level type-0 alpha^-1s
		(if not a0 && bexh then
		--if it's time to start generating alphas, but the type-0 alphas
		--haven't all been generated yet
		(map (newTT Alpha) . canonub . nexta0) tree else []) ++
		--then do just that
		(if agone then
		--finally, if it's time to generate the next level of alpha^-1
		(map (newabTT a Alpha) .canonub . nexta a) tree else[])
		--then do just that
		) True bexh (b+bint) (a+aint) lv state tree
		--set dcpop to true; set a0pop to true if bexh, i.e. if we've
		--started generating alphas (the alphas for not-a-product
		--notwithstanding); if we generated a new level of betas,
		--increment the beta level; do the same with the alpha; leave
		--the rest unchanged

--nextftree: Expands upon marked nodes
--This function is almost exactly the same as nexttree, so see the comments
--there for an explanation of how this works
--The only difference is that nextbb is called instead of nextb
--nextbb will not generate anything falling into the excluded infinite families
nextftree :: TreeTree -> TreeTree
nextftree tt@(TT False _ _ _ _ _ _ _ _) = tt
nextftree tt@(TT True kids dc a0 b a lv state tree) =
	let dgo = state == Delta
	    cgo = state >= Gamma
	    bgo = state >= Beta
	    bkids = filter (\x -> st x==Beta && lev x == b-1) kids
	    akids = filter (\x -> st x==Alpha && lev x == a-1) kids
	    bexh = maybe True (<b) (minlength tree)
	    bgone = bgo && (null bkids || any ls bkids)
	    agone = bexh && (null akids || any ls akids)
	    bint = if bgone then 1 else 0
	    aint = if agone then 1 else 0 in
		TT True (map nextftree kids ++
		(if not dc && dgo then
		maybe [] ((:[]) . (newTT Delta)) (delta tree) else []) ++
		(if not dc && cgo then
		(map (newTT Gamma) . canonub . gamma) tree else []) ++
		(if bgone then
		(map (newabTT b Beta) . canonub . nextbb b) tree else []) ++
		(if not dc && not (isprod tree) then
		(map (newTT Alpha) . canonub . mnexta0) tree else []) ++
		(if not a0 && bexh then
		(map (newTT Alpha) . canonub . nexta0) tree else []) ++
		(if agone then
		(map (newabTT a Alpha) . canonub . nexta a) tree else[])
		) True bexh (b+bint) (a+aint) lv state tree

--minlength: Given an expression, returns the length of the smallest product;
--returns a Maybe Integer, as Nothing represents infinity, i.e. no products
--without clumps
minlength :: APTTree -> Maybe Integer
minlength (PlusOne a) = minlength a
minlength OneLeaf = Nothing
minlength (Plus a b) = winf min (minlength a) (minlength b)
minlength (LTimes (Clump3 _ :l)) = l2ml minimum (map minlength l)
minlength (LTimes l) = winf min (Just (genericLength l))
	(l2ml minimum (map minlength l))

--SECTION 4: THE INVERSE TRANSFORMATIONS: DELTA AND GAMMA

--delta: Computes delta^-1.  Because delta^-1 is (if it exists) unique, just
--returns a Maybe APTTree; the others will return an [APTTree].  Because delta
--is only ever done right at the beginning, we only have two cases to worry
--about, depending on whether we're in the abstract case or the concrete case.
--NOTE that this function assumes the derived order on APTTrees!  (Well, it
--possibly does, anyway.)
delta :: APTTree -> Maybe APTTree
delta (LTimes (Clump3 n:rest)) =
	Just (LTimes(Clump3 (n+2) : twoLeaf : twoLeaf : twoLeaf : rest))
delta (LTimes (PlusOne (PlusOne OneLeaf):PlusOne (PlusOne OneLeaf):rest)) =
	Just (LTimes (twoLeaf : twoLeaf : twoLeaf : rest))
--in the concrete case, enough deltas will eventually result in something
--un-delta-able
delta _ = Nothing


--gamma: Returns a list of all possible gamma^-1s of the given expression.  Its
--actual function is relegated to two helper functions, gamma3 and gamma4, each
--of which produce different parts of the list.  (There was once a gamma2
--function, hence the names.)
gamma :: APTTree -> [APTTree]
gamma t = gamma3 t ++ gamma4 t

--gamma3: This part of gamma takes care of combining clumps with themselves -
--rather, that is, taking two threes out a single clump and combining them.
--(This does not need a concrete analogue; anything not involving clumps will be
--handled by gamma4.  Delta is the only one of the four inverse transformations
--that needs to be modified for the concrete case.)
gamma3 :: APTTree -> [APTTree]
gamma3 (LTimes []) = [] --meaningless, but necessary for recursion
gamma3 (LTimes ((Clump3 n):xs)) = [LTimes (Clump3 (n+2):constLeaf 6:xs)] ++
	((ltmap (Clump3 n:) . gamma3 . LTimes) xs)
gamma3 (LTimes (x:xs)) = (ltmap (x:) . gamma3 . LTimes) xs
--in the concrete case, a gamma can eventually result in something not a
--product, rendering it un-gamma-able
gamma3 _ = []

--gamma4: This part of gamma takes care of combining different elements of a
--product (i.e. not a clump with itself).
--subsets 2 picks out all possible pairs from l, and gamhelp does the rest
gamma4 :: APTTree -> [APTTree]
gamma4 (LTimes l) = (map (uncurry gamhelp) . subsets 2) l
--in the concrete case, a gamma can eventually result in something not a
--product, rendering it un-gamma-able
gamma4 _ = []

--gamhelp: Helper function for gamma4
--takes a list of two APTTrees and adds them with chainadd
--then concatenates this with the second list of APTTrees
--then interprets the whole thing as a list of factors for LTimes
gamhelp :: [APTTree] -> [APTTree] -> APTTree
gamhelp [m,n] l = LTimes (chainadd m n ++ l)

--chainadd: Takes two APTTrees and adds them together; i.e. it performs
--[m] [n] |-> [m+n]
--it returns a list of APTTrees, because if one of m or n is a clump, it returns
--the modified clump (one 3 has been pulled out) as well as the sum
--(for pulling two 3s out of a clump and adding them together, see gamma3)
--This function assumes we don't hit two clumps!
--It also assumes that both its arguments are either
--A. a clump or
--B. a chain of PlusOnes terminating in a OneLeaf
--(as they should be at this stage, if gamma is being applied!)
chainadd :: APTTree -> APTTree -> [APTTree]
chainadd OneLeaf OneLeaf = [PlusOne OneLeaf]
chainadd (PlusOne a) OneLeaf = [PlusOne (PlusOne a)]
chainadd OneLeaf (PlusOne b) = [PlusOne (PlusOne b)]
chainadd (PlusOne a)(PlusOne b)= [(PlusOne . head) (chainadd (PlusOne a) b ) ]
chainadd (Clump3 n) a = [Clump3 (n+1),PlusOne(PlusOne(PlusOne(a)))]
chainadd a (Clump3 n) = [Clump3 (n+1),PlusOne(PlusOne(PlusOne(a)))]

--SECTION 5: THE INVERSE TRANSFORMATIONS: BETA AND ALPHA

--nextb: takes an integer (stage) and an APTTree, and returns all beta^-1s of
--that expression of the given stage
nextb :: Integer -> APTTree -> [APTTree]
nextb _ OneLeaf = []
nextb n (PlusOne a) = map PlusOne (nextb n a)
nextb _ (Clump3 _) = [] --why is this [], when, well, that's wrong?
			--the answer to this is to consider what context such a
			--call would actually occur in.  Whatever this clump is,
			--it occurs within a product, and producing the results
			--of this will be handled by the call of nextb on that
			--product.
nextb n (LTimes l) = (map LTimes . concatMaponce (nextb n)) l ++
	concatMap ((uncurry . flip . pullup) n) (tsubsets n l)
--the first operand of the ++ is just recursion on the factors and concatenating
--these together
--the second operand of the ++ is the actual operation of nextb; tsubsets n
--extracts the subsets of size n (and their complements); then we do (uncurry .
--flip .  pullup) n on each one to get all possibilities, and concatenate those
--together
--NOTE the flip on the pullup!  This is because tsubsets returns subsets of size
--n FIRST and their complements SECOND, while pullup expects them the other way
--around.  Yes, this is kind of dumb.  No, I'm not changing it.

--pullup: Given an integer (stage), and two lists of factors for an LTimes,
--finds all possible ways of pulling up a one from the SECOND (see note above!)
--and combining this with the first into an LTimes.  I.e. it's all ways of doing
--a beta^-1 with the third argument the group that is having a 1 pulled up from
--it and the second argumen the rest of the factors.
pullup :: Integer -> [APTTree] -> [APTTree] -> [APTTree]

pullup n l m=let k=n-nonclumps m
--k: n is the stage.  If m does not contain a clump, then it has length
--precisely n.  If it does contain a clump, however, then it need not, and we
--need to know just how many threes are getting pulled out of that clump.  This
--is given by n-nonclumps m.
		 (cl,l2)=partition isclump (m++genericReplicate k threeLeaf) in
--(l2,cl): Now that we know k, let's tack on k threes to l to make l2 (the clump
--itself is not in the pullup, just k of its threes) and filter out the clump
--from it, sticking it in a singleton list cl if it exists (if there is no
--clump, k=0 and cl is empty)
			(map (\x -> LTimes (l++map (declump k) cl++
			[(PlusOne . LTimes) x])) .
			pulluphelp) l2
--now, we take our list to pullup, and map pulluphelp over it (which actually
--does the pulling up), then for each of the resulting possibilities we stick it
--under an LTimes and a PlusOne, then add back in the clump (with k threes
--removed) (if it exists) and the argument l, then stick the whole thing under
--an LTimes.

--declump: removes threes from a clump, leaves other things alone
declump :: Integer -> APTTree -> APTTree
declump k (Clump3 n) = Clump3 (n+k)
declump _ t = t

--pulluphelp: Given a list of factors from which a one is to be pulled up, pull
--up a one in all possible ways and return the list of results (note, this
--function just removes the one, it's added back in in pullup)
pulluphelp :: [APTTree] -> [[APTTree]]
pulluphelp [] = [] --meaningless, but needed for the recursion
pulluphelp (PlusOne OneLeaf:ts)=map (twoLeaf:) (pulluphelp ts)
--don't pull up from a two!  The result would leave a one in the product; but
--that would mean that, running the transformations in the forward direction,
--alpha would get done next, not beta - hence this is not among the beta^-1
--possibilities
pulluphelp (PlusOne (LTimes l):ts) = map (PlusOne (LTimes l):) (pulluphelp ts)
--don't pull up a PlusOne LTimes, either, as the result would not beta to what
--we start with - the result would be a merging of two products, and applying
--beta, that product would be preserved, not split to get this two-level product
pulluphelp (PlusOne a:ts) = (a:ts):map (PlusOne a:) (pulluphelp ts)
--otherwise, get rid of a one
pulluphelp (t:ts) = map (t:) (pulluphelp ts)
--leave other things alone

--nexta0: Given an APTTree, computes all type-0 alpha^-1s of it
nexta0 :: APTTree -> [APTTree]
nexta0 OneLeaf = []
nexta0 (Clump3 n) = [LTimes [Clump3 (n+1),twoLeaf]]
nexta0 (PlusOne a) = (a:map PlusOne (nexta0 a))
nexta0 (Plus a b) = map (Plus a) (nexta0 b) ++ map (flip Plus b) (nexta0 a)
nexta0 (LTimes l) = (map LTimes . concatMaponce nexta0) l

--mnexta0: Given an APTTree, compute all type-0 alpha^-s in it that take place
--above any product
mnexta0 :: APTTree -> [APTTree]
mnexta0 OneLeaf = []
mnexta0 (LTimes _) = []
mnexta0 (Clump3 _) = []
mnexta0 (PlusOne a) = (a:map PlusOne (nexta0 a))
mnexta0 (Plus a b) = map (Plus a) (mnexta0 b) ++ map (flip Plus b) (mnexta0 a)

--given an integer (stage) and an APTTree, computes all alpha^-1s of that
--APTTree of the given stage
nexta :: Integer -> APTTree -> [APTTree]
nexta _ OneLeaf = []
nexta _ (Clump3 n) = []
nexta n (PlusOne a) = map PlusOne (nexta n a)
nexta n (Plus a b) = map (Plus a) (nexta n b) ++ map (flip Plus b) (nexta n a)
nexta n (LTimes l) = if any isclump l then [] else
	--if there's a clump, don't do alpha^-1s!
	(map LTimes . concatMaponce (nexta n)) l ++
	--first operand of ++: recurse on the factors
	((map . uncurry) Plus .
	(filter . uncurry) (\x y -> val x <= val y) .
	map1 LTimes . map2 LTimes .
	(pairfilter . any) (/=OneLeaf))
	(subsets n l)
	--this block of code computes the actual alpha^-1; subsets n l takes
	--all subsets of size n, and their complements; then, we make sure
	--neither consists of all ones - if either did, this wouldn't be an
	--alpha^-1!  (note we don't have to worry about products of value one
	--since we're assuming none of the factors are themselves products)
	--Then, we stick an LTimes on each of the lists, and make sure that the
	--numerical value on the left is no larger than that on the right (so
	--that the stage is, in fact, correct); then we add the two parts
	--together.
	--NOTE that this code has been considerably simplified by the assumption
	--that we are never going to attempt to do an alpha^-1 on a product
	--containing a clump.

--nextbb: Modified nextb.  It's nextb, except that it excludes anything of the
--infinite families in the paper.  In most cases - when none of the children
--will be in one of those families - it simply calls nextb.  When some but not
--all of the children are, it calls nextb, then removes the offenders.  When
--all of the children are, it just returns [].  Note that it only deletes
--elements of the families that could actually be generated by the call to
--nextb. NOTE also that we've been slightly sloppy here - we haven't checked the
--congruence class of what we're working, which means that, e.g., LTimes [Clump3
--0] could mean k=2 (mod 3), but we've done two type-0 alphas and lost two ones!
--However, this is irrelevant, as if we do even a single type-0 alpha and throw
--away even a single one, we'll have dropped to a value of at most (lambda_k)x,
--and therefore we won't be expanding on that node, so that situation never
--comes up.
nextbb :: Integer -> APTTree -> [APTTree]
--generates only 3^(Z-n)*(1+2*3^(n-1))
nextbb _ (LTimes [Clump3 0]) = []
--generates only 3^(Z-n)*2*(1+2*3^(n-1)) & 3^(Z-n)*(1+2^2*3^(n-2))
nextbb _ (LTimes [Clump3 0, PlusOne OneLeaf]) = []
--generates 3^(Z-n+1)*(1+3^n)
nextbb n t@(LTimes [Clump3 0, PlusOne (PlusOne (PlusOne OneLeaf))]) =
	delete (canonpermute
	(LTimes [Clump3 (n-1),
	PlusOne (LTimes (genericReplicate n threeLeaf))]))
	(canonub (nextb n t))
--generates 3^(Z-n-1)*2*(1+3^n) & 3^(Z-n)*(1+2*3^(n-1))
nextbb n t@(LTimes [Clump3 2, PlusOne (PlusOne (PlusOne OneLeaf)),
	PlusOne OneLeaf]) =
	(canonub (nextb n t)) \\ map canonpermute [
	LTimes [Clump3 (n+1), twoLeaf,
	PlusOne (LTimes (genericReplicate n threeLeaf))],
	LTimes [Clump3 n,
	PlusOne (LTimes (twoLeaf:genericReplicate (n-1) threeLeaf))]]
--generates 3^(Z-n-1)*2*2*(1+3^n) & 3^(Z-n)*2*(1+2*3^(n-1)) &
--3^(Z-n+1)*(1+2*2*3^(n-2))
nextbb n t@(LTimes [Clump3 2, PlusOne (PlusOne (PlusOne OneLeaf)),
	PlusOne OneLeaf, PlusOne OneLeaf]) =
	(canonub (nextb n t)) \\ map canonpermute [
	LTimes [Clump3 (n+1), twoLeaf, twoLeaf,
	PlusOne (LTimes (genericReplicate n threeLeaf))],
	LTimes [Clump3 n, twoLeaf,
	PlusOne (LTimes (twoLeaf:genericReplicate (n-1) threeLeaf))],
	LTimes [Clump3 (n-1),
	PlusOne (LTimes (twoLeaf:twoLeaf:genericReplicate (n-2) threeLeaf))]]
--generates 3^(Z-n-1)*4*(1+3^n) & 3^(Z-n)*(1+4*3^(n-1))
nextbb n t@(LTimes [Clump3 2, PlusOne (PlusOne (PlusOne OneLeaf)),
	PlusOne (PlusOne (PlusOne OneLeaf))]) =
	(canonub (nextb n t)) \\ map canonpermute [
	LTimes [Clump3 (n+1), constLeaf 4,
	PlusOne (LTimes (genericReplicate n threeLeaf))],
	LTimes [Clump3 n,
	PlusOne (LTimes (constLeaf 4:genericReplicate (n-1) threeLeaf))]]
--generates 3^(Z-n)*(1+4*3^(n-1))
nextbb n t@(LTimes [Clump3 1, PlusOne (PlusOne (PlusOne (PlusOne OneLeaf)))])=
	delete (canonpermute
	(LTimes [Clump3 n,
	PlusOne (LTimes (constLeaf 4:genericReplicate (n-1) threeLeaf))]))
	(canonub (nextb n t))
nextbb n t = nextb n t

--SECTION 6: ANSWER EXTRACTION

--orderedpicks: this is just picklist, but sorted and uniq'd - NOTE it's by
--rcmpval, so the highest value is FIRST
orderedpicks :: TreeTree -> [APTTree]
orderedpicks = nub . sortBy rcmpval . map canonpermute . picklist

--cfinalval: concrete final value; looks at the ordered picklist, and picks out
--the last one
cfinalval :: TreeTree -> Integer
cfinalval = aff2int . val . last . orderedpicks

--pickedvals: this is the list of picked values, sorted and uniq'd - NOTE this
--is not reversed; highest value is LAST
pickedvals :: TreeTree -> [Affine Rational]
pickedvals = nub . sort . map val . picklist

--afinalval: abstract (unadjusted) final value; looks at the list of values,
--take the *2nd* (since in the abstract case we went one further so we could
--get the minimum 3s) - then we have to adjust it, too
afinalval :: TreeTree -> Affine Rational
afinalval = head . tail . pickedvals

--adjfinalval: adjusted final value
adjfinalval :: Mod3 -> TreeTree -> Affine Rational
adjfinalval a = valadjust (g1adjust a) . afinalval

--final3s: for each value on the picklist (except the extraneous last one),
--looks at all expressions of that value, finds the minimum # of 3s to generate
--that value; then takes the max of these (as we need to generate them all)
final3s :: TreeTree -> Integer
final3s = maximum . map (minimum . map threes) . init . sortedpartition val .
	orderedpicks 

--finalbound: Given the # of 3s, how many 1s does that translate to?
finalbound :: Mod3 -> TreeTree -> Integer
finalbound a tt = 3*final3s tt + plusalso a

--cfinalresult: g_r(k) - the FINAL RESULT for the concrete case
cfinalresult :: Integer -> Integer -> Integer
cfinalresult r k = cfinalval (cfinalTT r k)

--finalresult: an ordered pair with both the final value and the number of 3s
--required; the FINAL RESULT for the abstract case
finalresult :: Integer -> Mod3 -> (Affine Rational, Integer)
finalresult r a = let t = finalTT r a in (adjfinalval a t, finalbound a t)

--tt2m1: takes a TreeTree and strips away most of the information to leave just
--a tree of values & numbers of 3s; also takes a Mod3 so as to adjust the values
tt2m1 :: Mod3 -> TreeTree -> MTree (APTTree,Affine Rational,Integer)
tt2m1 m (TT _ kids _ _ _ _ _ _ tree) =
	M1 (tree,(relval m tree),(threes tree)) (map (tt2m1 m) kids)

--thoroughfinal: the tt2m1 of the final TreeTree for the modified abstract
--("thorough") version, then we strip out the leaves to leave only the things
--with value above (lambda_m)x - the FINAL RESULT for that case
thoroughfinal :: Mod3 -> MTree (APTTree,Affine Rational,Integer)
thoroughfinal m = (stripleaves . tt2m1 m . thoroughTT) m

-- ...and we're done!  If we're working in an interpreter, cfinalresult,
-- finalresult, and thoroughfinal are our final results (as due to the
-- declaration that Mod3 is an instance of Num, integers input will
-- automatically be mod3'd, and of course the output will automatically be
-- show'd.)  otherwise...

--SECTION 7: I/O

--use whichever version of main is appropriate

main :: IO ()

--concrete version
{-
main =	do l <- getArgs
	   if length l <= 1 then hPutStrLn stderr "2 arguments required"
	   else (print . cfinalresult (read (head l)) . read) (l !! 1)
-}

{-
--abstract version
main =	do l <- getArgs
	   if length l <= 1 then hPutStrLn stderr "2 arguments required"
	   else (print . finalresult (read (head l)) . mod3 . read) (l !! 1)
-}

--thorough version
--{-
main =	do l <- getArgs
	   if null l then hPutStrLn stderr "Argument required"
	   else (print . thoroughfinal . mod3 . read . head) l
---}
