>module Useful (
>  hd, tl, member, findRepeats, flatmap, allEqual, (\\), remove, copy, inits, 
>  sortremdups, sortremdupsconcat, remdupsmerge, remdups, labelFront,
>  labelBack, myisAlphanum, spaces, intersection, subset, 
>  multiInstances, listMultiples, diffOneInstance, equalityLists, 
>  replicateListInc, remdupsf)
>where

>import Char

=========================================================================
Removal of duplicates

>remdups :: Eq a => [a] -> [a]
>remdups [] = []
>remdups (a:as) = a : remdups (filter (/= a) as)

>remdupsf :: Eq b => (a -> b) -> [a] -> [a]
>remdupsf f [] = []
>remdupsf f (a:as) = a : remdupsf f (filter (\ b -> f a /= f b) as)

Sort and remove duplicates

>sortremdups :: Ord a => [a] -> [a]
>sortremdups [] = []
>sortremdups [x] = [x]
>sortremdups xs = 
>  remdupsmerge (sortremdups (take n xs)) (sortremdups (drop n xs))
>    where n = div (length xs) 2

Merge two ordered lists without duplicates, removing duplicates

>remdupsmerge :: Ord a => [a] -> [a] -> [a]
>remdupsmerge [] xs = xs
>remdupsmerge xs [] = xs
>remdupsmerge (x:xs) (y:ys)
>  | x < y     = x : remdupsmerge xs (y:ys)
>  | x > y     = y : remdupsmerge (x:xs) ys
>  | x == y    = x : remdupsmerge xs ys

>sortremdupsconcat :: Ord a => [[a]] -> [a]
>sortremdupsconcat = foldr remdupsmerge []

=========================================================================
A few useful functions

>hd :: [a] -> a
>hd = head
>tl :: [a] -> [a]
>tl = tail

>(\\) :: Eq a => [a] -> [a] -> [a]
>xs \\ [] = xs
>xs \\ (y:ys) = remove xs y \\ ys

>remove :: Eq a => [a] -> a -> [a]
>remove [] _ = []
>remove (x:xs) y
>  | x==y        = remove xs y
>  | otherwise   = x:remove xs y

>copy :: a -> Int -> [a]
>copy x n = replicate n x

>member :: Eq a => a -> [a] -> Bool
>member = elem

>findRepeats :: Eq a => [a] -> [a]
>findRepeats [] = []
>findRepeats (x:xs) = if x `member` xs then (x:findRepeats xs) else (findRepeats xs)

>flatmap :: (a -> [b]) -> [a] -> [b]
>flatmap f = concat . map f

>allEqual :: Eq a => [a] -> Bool
>allEqual [] = True
>allEqual (x:xs) = all (== x) xs

All initial segments

>inits :: [a] -> [[a]]
>inits [] = [[]]
>inits (x:xs) = [] : map (x:) (inits xs)

Add a common label to the front of each string in a list of strings

>labelFront :: String -> [String] -> [String]
>labelFront _ [] = []
>labelFront s (x:xs) = (s++x):labelFront s xs

Add a common label to the end of each string in a list of strings

>labelBack :: String -> [String] -> [String]
>labelBack _ [] = []
>labelBack s (x:xs) = (x++s):labelBack s xs

>spaces :: Int -> String
>spaces n = replicate n ' '

Intersection of two lists

>intersection :: Eq a => [a] -> [a] -> [a]
>intersection [] _ = []
>intersection _ [] = []
>intersection l1 (l:ls) = if member l l1 then l:intersection l1 ls
>			  else intersection l1 ls

Subset definition for lists

>subset :: Eq a => [a] -> [a] -> Bool
>subset l1 l2 = (intersection l2 l1) == l1

MultiInstances l ls returns true if there is more than one instance
of l in ls.

>multiInstances :: Eq a => a -> [a] -> Bool
>multiInstances l as = length(as\\[l]) < length as - 1

>listMultiples :: Eq a => [a] -> [a]
>listMultiples [] = []
>listMultiples xs = listM xs (remdups xs)
>	where	listM _ [] = []
>		listM xs (y:ys) = if (multiInstances y xs) 
>				  then y:listM xs ys
>				  else listM xs ys

diffOneInstance ls xs removes the elements xs from ls mapping
one-on-one instances.  For example, 

	diffOneInstance [1,1,2,3] [1,2] = [1,3]
whereas
	[1,1,2,3]\\[1,2] = [3]

>diffOneInstance :: Eq a => [a] -> [a] -> [a]
>diffOneInstance ls [] = ls
>diffOneInstance ls (x:xs) = diffOneInstance (rem x ls) xs
>	where
>		rem _ [] = []
>		rem x (l:ls) =	if (x==l) then ls
>				else l:rem x ls

>replicateListInc :: Int -> String -> [String]
>replicateListInc n str = [str++show i++"_" | i <- [1..n]]

Equality of 2 lists in terms of the members, regardless of order and
duplications.  For example, 

	equalityLists [1,2,3] [3,2,1] = True, whereas

	[1,2,3] == [3,2,1] = False.

>equalityLists :: Eq a => [a] -> [a] -> Bool
>equalityLists xs ys = elemMember xs ys && elemMember ys xs

>elemMember :: Eq a => [a] -> [a] -> Bool
>elemMember _ [] = True
>elemMember xs (y:ys) = member y xs && elemMember xs ys

Note: equalityLists [1,1,1,2,3] [3,2,1] = True, since we do not take
duplicates into account (function mainly used in DataIndep.lhs).


----- For hugs 98 purposes ---------------

>myisAlphanum :: Char -> Bool
>myisAlphanum c = isAlpha c || isDigit c



