>module MiscParse 
> (Line, TypeType(AtomType, FnType),
>  tokenize, dropEmptyLines, split, select,
>  allAlphaNum, dropWhite, isWhite, isNum, parseInt, comment,
>  termed_comma_list, comma_list, parseCommaList) 
>where

Misc text parsing functions

>import Char
>import Useful
>import Maybe1
>import GenParse
>import Atoms

>type Line = String

>data TypeType = AtomType TypeName | FnType [TypeName] TypeName
>                deriving Show


>isWhite c = c == ' ' || c == '\t' || c == '\n'
>dropWhite :: [Char] -> [Char]
>dropWhite = filter (not . isWhite)
>dropEmptyLines :: [[Char]] -> [[Char]]
>dropEmptyLines = filter ((/= []) . dropWhite)
>comment line = length line >= 2 && take 2 line == "--"

Split line about next white space

>splitWhite :: Line -> (Line, Line)
>splitWhite ls =
>  (takeWhile (not . isWhite) ls , (dropWhite . dropWhile (not . isWhite)) ls)

>isPunct c = member c ",:;.()[]{}=->"
>dropPunct :: [Char] -> [Char]
>dropPunct = filter (not . isPunct)

>isWhiteOrPunct c = isWhite c || isPunct c 

>allAlphaNum = all myisAlphanum


>isNum = all (\c -> c >= '0' && c <= '9')
>parseInt = foldl foo 0 . map (\c -> ord c - ord '0')
>  where foo n m = 10 * n + m

Split line about next white space

>splitPunct :: Line -> (Line, Char, Line)
>splitPunct ls 
>  | rest /= ""    = (takeWhile (not . isPunct) ls , hd rest, tl rest)
>  | rest == ""    = (takeWhile (not . isPunct) ls , '\n', "")
>  where rest = dropWhile (not . isPunct) ls

Take tokens representing string of form "(A,na,pka,ska,S,pks)" and return list 
["A","na","pka","ska","S","pks"]

>getargs :: Line -> [String] -> Maybe_ [String]
>getargs l0 ("(":cs) =
>  fst @@
>  checkM (parseCommaList l0 ")" cs)
>         (\ (_,rest) -> rest == [], 
>          "Error: unexpected characters: " ++ l0 ++ "\n")
>getargs l0 _ = Error ("Error: bad arguments: " ++ l0)

Parse comma-separated list, up to character terminator, returning warning,
list of arguments, and remains

>parseCommaList :: Line -> String -> [String] -> Maybe_([String], [String])
>parseCommaList l0 terminator (t : ts) 
>  | terminator == t   = Yes ([], ts)
>  | otherwise         = parseCommaList1 l0 terminator (t : ts)

>parseCommaList1 :: Line -> String -> [String] -> Maybe_([String], [String])
>parseCommaList1 _ terminator (a : term' : ts)  
>  | terminator == term' && allAlphaNum a              = Yes ([a], ts)
>parseCommaList1 l0 terminator (a : "," : ts) 
>  | allAlphaNum a         = consfirst a @@ parseCommaList1 l0 terminator ts
>  where consfirst a (args, rest) = (a:args, rest)
>parseCommaList1 l0 _ ts = 
>  Error ("Error: bad arguments: "++show ts++" in "++l0)

Now using combinatorial parsing

termed_comma_list term_char = ::= variable "," comma_list | term_char

>termed_comma_list :: Char -> Parse Char [String]
>termed_comma_list termchar = 
>  word ^^^termed_comma_list' termchar >>> (\ (w, ws) -> w:ws)
>termed_comma_list' termchar = 
>  tokenws termchar >>> (\ _ -> [])
>  ||| 
>  tokenws ',' ^^^ word ^^^ termed_comma_list' termchar >>> makelist
>  where makelist (_, (w, ws)) = w:ws

>comma_list :: Parse Char [String]
>comma_list = word ^^^ comma_list' >>> (\ (w, ws) -> w:ws)
>comma_list' =
>  tokenws ',' ^^> wordws ^^^ comma_list' >>> (\ (w, ws) -> w:ws)
>  |||
>  succeed []


Split into tokens, defined to be contiguous alphanumerics, or single
punctuation characters, possibly separated by white space

>tokenize :: Line -> [String]
>tokenize "" = []
>tokenize (c:cs) 
>  | isWhite c       = tokenize cs
>  | isPunct c       = [c]: tokenize cs
>  | myisAlphanum c    = (c: takeWhile myisAlphanum cs) 
>                      : tokenize (dropWhile myisAlphanum cs)
>  | otherwise       = [c] : tokenize cs

==========================================================================
Functions for splitting input into different sections

>isKeyword :: Line -> Bool
>isKeyword [] = False
>isKeyword (c:_) = c == '#'


Get all lines up to but not including next line starting with key word

>getSection :: [Line] -> ([Line], [Line])
>getSection ls = 
>  (takeWhile (not . isKeyword) ls, dropWhile (not . isKeyword) ls)

Split into sections defined by keywords

>split :: [Line] -> [(String, [Line])]
>split ls = ("#Preamble", dropEmptyLines sect) : split1 rest
> where (sect, rest) = getSection ls

>split1 [] = []
>split1 (l:ls) = (dropWhite l, dropEmptyLines sect) : split1 rest
> where (sect, rest) = getSection ls

>select :: Eq a => a -> [(a, [Line])] -> [Line]
>select s klss 
>  | matches == []    = []
>  | otherwise        = hd matches
> where matches = [ls | (s',ls) <- klss, s' == s]
