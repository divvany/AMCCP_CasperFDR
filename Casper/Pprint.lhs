>module Pprint (
>  commaConcat, dotConcat, termConcat, nlConcat, commaNlConcat,
>  opConcat, format, heading, indentHeading, makeComment,
>  makeLogicalLines, makeUnion, makeUnion', makeUnionOneLine, maybeString
>  )

>where

>import Useful

============================================================================
Printing functions

>maybeString :: Bool -> String -> String
>maybeString True st = st
>maybeString False _ = ""

>colwidth :: Int
>colwidth = 75

Print main heading

>heading h = 
>  let w = length h
>      s1 = (colwidth - w - 5) `div` 2
>      s2 = colwidth - w - 5 - s1
>  in "-- " ++ copy '*' (colwidth -3) ++ "\n" ++ 
>     "-- *" ++ spaces s1 ++ h ++ spaces s2 ++ "*\n" ++
>     "-- " ++ copy '*' (colwidth -3) ++ "\n\n"

>indentHeading n h = 
>  let w = length h
>      s1 = (colwidth - w - 5 - n) `div` 2
>      s2 = colwidth - w - 5 - s1 - n
>  in spaces n ++ "-- " ++ copy '*' (colwidth-3-n) ++ "\n" ++ 
>     spaces n ++ "-- *" ++ spaces s1 ++ h ++ spaces s2 ++ "*\n" ++
>     spaces n ++ "-- " ++ copy '*' (colwidth-3-n) ++ "\n\n"

Turn string into comment, by splitting into lines of length at most 
colwidth-3, and prefixing each line with n spaces and "-- "

>makeComment :: Int -> String -> String
>makeComment n st = 
>  let lines = splitLines n "" "" (words st)
>  in  lines

Split list of words into lines, accumulating current line in l, and complete
result in st

>splitLines :: Int -> String -> String -> [String] -> String 
>splitLines n l st [] = st++makeC n l
>splitLines n l st (w:ws) =
>  if length l+length w+3+n > colwidth 
>  then splitLines n "" (st++makeC n l) (w:ws)
>  else splitLines n (l++" "++w) st ws

>makeC n l = spaces n++"--"++l++"\n"

>commaConcat [] = ""
>commaConcat sts = foldr1 comma sts
> where comma xs ys = xs ++ ", " ++ ys

>dotConcat = foldr1 dot
> where dot xs ys = xs ++ "." ++ ys

>nlConcat n [] = []
>nlConcat n zs = foldr1 nl zs
> where nl xs ys = xs ++ "\n" ++ copy ' ' n ++ ys

>commaNlConcat n = foldr1 commaNl
> where commaNl xs ys = xs ++ ",\n" ++ copy ' ' n ++ ys

>termConcat = foldr1 term
> where term xs ys = xs ++ " | " ++ ys

>opConcat _ [] = ""
>opConcat op sts = foldr1 (f op) sts
> where f op xs ys = xs ++ op ++ ys

Format list of strings to fit in column of width n, separating items with
separator

>prettyPrint :: Int -> String -> [String] -> [String]
>prettyPrint _ _ [] = []
>prettyPrint n separator (st:sts) = pp st sts
> where pp line [] = [line]
>       pp line (st:sts)
>         | length line + length st > n  
>                        = (line ++ separator ++ "\n") : pp st sts
>         | otherwise    = pp (line ++ separator ++ st) sts

Print each string, prefixed by n spaces

>prefixStrings :: Int -> [String] -> String
>prefixStrings _ [] = ""
>prefixStrings n sts = foldr1 foo sts
>  where foo st st' = st ++ copy ' ' n ++ st'

>format :: Int -> String -> [String] -> String
>format indent separator = 
>  prefixStrings indent . 
>  prettyPrint (colwidth - indent - length separator) separator

================= Misc things, that probably shouldn't be here

print union, indenting by n spaces

>makeUnion :: Int -> [String] -> String
>makeUnion _ [] = "{}\n"
>makeUnion n [a] = 
>  (if length a > colwidth-25 then "\n"++copy ' ' n else "")++a++"\n"
>makeUnion n as
>  | longline  = "\n"++spaces n++"Union({\n"++spaces (n+2)++
>                commaNlConcat (n+2) as++"\n"++ spaces n++"})\n"
>  | otherwise = "Union({"++commaConcat as++"})\n"
>  where
>        longline = 2 * length as + sum (map length as) + n + 20 > colwidth

the same as make union but without the newline at the start and end

>makeUnion' :: Int -> [String] -> String
>makeUnion' _ [] = "{}"
>makeUnion' n [a] = 
>  (if length a > colwidth-25 then "\n" ++ copy ' ' n else "")++a
>makeUnion' n as
>  | longline  = "Union({\n"++spaces (n+2)++
>                commaNlConcat (n+2) as++"\n"++ spaces n++"})"
>  | otherwise = "Union({"++commaConcat as++"})"
>  where
>        longline = 2 * length as + sum (map length as) + n + 20 > colwidth

>makeUnionOneLine :: [String] -> String
>makeUnionOneLine [] = "{}"
>makeUnionOneLine [a] = a
>makeUnionOneLine [a,b] = "union("++a++", "++b++")"
>makeUnionOneLine as = "Union({"++commaConcat as++"})"

Combine lines where first ends in "\"

>makeLogicalLines [] = []
>makeLogicalLines [l] = [l]
>makeLogicalLines (l1:l2:ls)
>  | l1 /= "" && last l1 == '\\'   = (init l1 ++ hd ls') : tl ls'
>  | isIndented l2                 = (l1 ++ hd ls') : tl ls'
>  | otherwise                     = l1 : ls'
>  where 
>       ls' = makeLogicalLines (l2:ls)
>       isIndented ('\t':_) = True
>       isIndented (' ':_) = True
>       isIndented _ = False
