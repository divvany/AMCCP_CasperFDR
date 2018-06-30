numGeneric parsing functions

>module GenParse (
>  Parse, succeed, token, spot, (|||), (^^^), (<^^), (^^>), (>>>), 
>  check, optional, optional1, into, eol,
>  many, listOf, topLevel, topLevel1, 
>  white, tokenws, ws, word, wordws, word1, word1ws, number, cons,
>  dword, dwordws)
>where

>import Char
>import Maybe1
>import Useful

---------------------------------------------------
-- Combinatory parsing library using Maybe types --
--     suitable for non-ambiguous grammars.      --
--         sja4@mcs.le.ac.uk (21/10/96)          --
---------------------------------------------------
Adapted by Gavin

>infixr 5 `thn`, `xthn`, `thnx`, `into`, ^^^, <^^, ^^>
>infixl 4 `build`, >>>
>infixr 3 `alt`, |||

---------------------
-- Type of parsers --
---------------------

>type Parse a b = [a] -> Maybe (b,[a])

-------------------
-- Basic parsers --
-------------------

Succeed with the value given.

>succeed :: b -> Parse a b
>succeed val inp = Just (val, inp)

Recognize a specified token at the head of the input.

>token :: Eq a => a -> Parse a a
>token t (u:x) = if t == u then Just (t,x) else Nothing
>token _ [] = Nothing

Recognize a token with a certain property.

>spot :: (a -> Bool) -> Parse a a
>spot p (t:x) = if p t then Just (t,x) else Nothing
>spot _ [] = Nothing

Matches the end of a sequence

>eol :: Parse a ()
>eol (x:xs) = Nothing
>eol [] = Just ((),[])

-------------------------
-- Parsing combinators --
-------------------------

A choice between two parsers. The function alt p1 p2 returns the result of p1
whenever it succeeds and the result of p2 otherwise.

>alt :: Parse a b -> Parse a b -> Parse a b
>alt p1 p2 inp = case p1 inp of
>		Nothing -> p2 inp
>		Just (v,x) -> Just (v,x)

>t ||| t' = t `alt` t'

Sequencing of parsers. The function thn p1 p2 returns the result, if any, of
applying p1 to the input and then p2 to the remainder.

>thn :: Parse a b -> Parse a c -> Parse a (b,c)
>thn p1 p2 inp = case p1 inp of
>		Nothing -> Nothing
>		Just (v,x) -> case p2 x of
>				Nothing -> Nothing
>				Just (u,y) -> Just ((v,u),y)

>t ^^^ t' = t `thn` t'

Semantic action. The results from a parser p are transformed by applying a
function f.

>build :: Parse a b -> (b -> c) -> Parse a c
>build p f inp = case p inp of
>		Nothing -> Nothing
>		Just (v,x) -> Just (f v, x)

>t >>> f = t `build` f

>check :: (a -> Bool) -> Maybe (a,b) -> Maybe (a, b)
>check p (Just (a, b)) | p a       = Just (a, b)
>                      | otherwise = Nothing
>check _ Nothing  = Nothing

>thnx :: Parse a b -> Parse a c -> Parse a b
>thnx p q = (p `thn` q) `build` fst

>t <^^ t' = t `thnx` t'

>xthn :: Parse a b -> Parse a c -> Parse a c
>xthn p q = (p `thn` q) `build` snd

>t ^^> t' = t `xthn` t'

First parse with p1, then with p2; if latter fails then just return result
from p1; else combine results with f

>optional :: Parse a b -> Parse a c -> ((b, c) -> b) -> Parse a b 
>optional p1 p2 f inp =
>  case p1 inp of
>    Nothing -> Nothing
>    Just (v,rest) -> 
>      case p2 rest of
>        Nothing -> Just (v,rest)
>        Just (v',rest') -> Just (f(v,v'), rest')

>optional1 :: Parse a b -> b -> Parse a b
>optional1 p1 e inp = 
>   case p1 inp of
>       Just (v,rest)   -> Just (v, rest)
>       Nothing         -> Just (e, inp)

Removed to avoid name clash:

number ::  Parse String Int
number = spot (all isDigit) `build` read

Repetition. The parser p is used as many times as possible and the results are
returned as a list.

>many :: Parse a b -> Parse a [b]
>many p = ((p `thn` many p) `build` cons) `alt` (succeed [])

ListOf p c applies parser p as many times as possible, with the instances
separated by instances of c, and returns the result as a list.

>listOf :: Eq a => Parse a b -> a -> Parse a [b]
>listOf p sep = 
>   p `thn` many (token sep `xthn` p) `build` cons

>cons (x,xs) = x:xs

The top level parser is a function which maps a list of tokens to a value. A
value p :: Parse a b can be converted to such a function by applying topLevel:

>topLevel :: Show a => Parse a b -> [a] -> b
>topLevel p inp
>  = case p inp of
>      Just (result,[]) -> result
>      Just (_,rest) -> 
>        error ("parse unsuccessful; input unconsumed:"++show rest)
>      _ -> error "parse unsuccessful"

>topLevel1 :: Parse Char b -> String -> String -> Maybe_ b
>topLevel1 p err inp =
>  case p inp of
>    Just (result,[]) -> Yes result
>    _ -> Error (err++"\n  "++inp++"\n")

Note there is an error if the input is not fully consumed.

It is sometimes useful to test whether a given parser will accept the input
without actually returning a result.

>acceptedBy :: Parse a b -> [a] -> Bool
>acceptedBy parser inp
>   = case parser inp of
>	Just (_,[]) -> True
>	_ -> False

A more sophisticated form of sequencing. The into combinator allows the second
parser to be chosen according the result of the first.
 
>into :: Parse a b -> (b -> Parse a c) -> Parse a c
>into p f inp = case p inp of
>		Nothing -> Nothing
>		Just (v,x) -> f v x

==========================================================================
Absorb white space

>white = many (token ' ' ||| token '\t')
>ws p = white ^^> p <^^ white
>tokenws t = white ^^> token t <^^ white 

==========================================================================

Consume and return arbitrary word

>word :: Parse Char String
>word = spot isAlpha ^^^ many (spot myisAlphanum) ^^^ many (token '\'') >>> cons_
> where cons_ (c, (cs, ps)) = c:cs++ps

>wordws = white ^^> word <^^ white 

Consume and return particular word

>word1 :: String -> Parse Char String
>word1 [c] = token c >>> (\ c -> [c])
>word1 (c:cs) = (token c ^^^ word1 cs) >>> cons

>word1ws w = ws (word1 w)

Consume and return number

>number :: Parse Char Int
>number = (tokenws '-' ||| succeed '+') ^^^ spot isDigit ^^^ many (spot isDigit) 
>   >>> (\ (mt, (d, ds)) -> if mt == '-' then -1 * mknum (d:ds) else mknum (d:ds))
> where mknum [] = 0
>       mknum ds = 10*mknum (init ds) + digitToInt (last ds)

Consume and return a word which may start with a digit

>dword :: Parse Char String
>dword = spot myisAlphanum ^^^many (spot myisAlphanum) ^^^ many (token '\'') >>> cons_
>  where cons_ (c, (cs, ps)) = c:cs ++ ps

>dwordws = white ^^> dword <^^ white

