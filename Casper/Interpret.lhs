sInterpret output produced by FDR

>module Interpret(interpret,linterpret) where

>import Char
>import Useful
>import Pprint
>import GenParse

Main functions, each of which interprets output from FDR, giving easier to
understand format.  interpret produces standard text; linterpret produces
LaTeX source for use with security.sty.

>interpret, linterpret :: IO()
>interpret = interpret1 False
>linterpret = interpret1 True

The latex flag represents whether output is required as LaTeX

>interpret1 :: Bool -> IO()
>interpret1 latex =
>  do ls <- getLines
>     -- putStr (show (combine ls))
>     putStr (produceOutput latex (combine ls)++"\nGoodbye\n")

Read lines until a blank one is found

>getLines :: IO [String]
>getLines =
>  do l <- getLine
>     if l == "" 
>      then return [] 
>      else do ls <- getLines
>              return (l:ls)

Get particular field from a line

>getFirstField, dropFirstField :: String -> String
>getFirstField = takeWhile (not . delim)
>dropFirstField st = 
>  let st' = dropWhile (not . delim) st
>  in if st'=="" then "" else tl st'

>delim c = c=='.' || c==',' || c=='}'

>getNthField 1 = getFirstField
>getNthField n = getNthField (n-1) . dropFirstField

>dropNFields 0 = id
>dropNFields n = dropNFields (n-1) . dropFirstField

>getAllFields "" = []
>getAllFields st = getFirstField st : getAllFields (dropFirstField st)

Combine lines that correspond to the same event

>combine :: [String] -> [String]
>combine [] = []
>combine (w:ws) = 
>  let this = w : takeWhile (not . startsWithKeyWord) ws
>      rest = dropWhile (not . startsWithKeyWord) ws
>  in foldr1 (\ st st' -> st++","++st') this : combine rest

>keyWords =
>  ["receive", "send", "internalAgentSend", "comm", "env", "signal", "leak",
>   "tock",  "_tau", "notknowit", "knowit",  "crack",
>   "close", "INTRUDER_M::spypick", "replace", "error", "outofsteam",
>   "deduce", "infer", "INTRUDER_M::guess", "INTRUDER_M::verify"]

"time",

>startsWithKeyWord l = member (getFirstField l) keyWords

========================================================================

Produce output

>data Event = Comm String String String String | FullLine String | None
>	      deriving (Show)

>produceOutput :: Bool -> [String] -> String
>produceOutput latex ls = 
>  let es = map (parseEvent latex) ls
>  in showOutput latex es

=======================================================================

Parse line corresponding to particular event, giving corresponding output
string

>parseEvent :: Bool -> String -> Event
>parseEvent latex l =
>  case getFirstField l of
>    -- "comm" ->
>    --   let (a,b,n,mstr) = splitcomm latex (dropFirstField l)
>    --   in Comm n a b mstr
>    "receive" ->
>      let (a,b,n,mstr) = splitcomm latex (dropFirstField l)
>      in Comm n (mkIntruder latex a) b mstr
>    "send" ->
>      let (a,b,n,mstr) = splitcomm latex (dropFirstField l)
>      in Comm n a (mkIntruder latex b) mstr
>    "internalAgentSend" ->
>      let (a,b,n,mstr) = splitcomm latex (dropFirstField l)
>      in Comm n a (mkIntruder latex b) mstr
>    "env" ->
>      let b = getNthField 2 l
>          n = (drop 3 . getFirstField . tl . dropFirstField .dropFirstField) l
>          m = (dropFirstField . dropFirstField . dropFirstField) l
>          mstr = topmsg latex m
>      in Comm n " " b mstr
>    "signal" -> (FullLine . parseSignal latex . dropFirstField) l
>    "leak" -> 
>      FullLine ("The intruder knows "++showMaths latex (getNthField 2 l))
>    -- "time" -> FullLine ("Time is "++getNthField 2 l)
>    "tock" -> FullLine ("Time passes")
>    "crack" -> 
>       let v = getNthField 2 l
>       in FullLine (showMaths latex v++" has been compromised")
>    "replace" -> 
>	let v = (drop 1 . getNthField 2) l
>	    b = (takeWhile (/= ')') . getNthField 3) l
>	in FullLine (showMaths latex v++" has been recycled to "++
>                    showMaths latex b++" in the intruder's " ++
>		     "memory and is therefore regarded as fresh again")
>    "INTRUDER_M::guess" -> 
>       let mstr = topLevel (msg latex) (dropFirstField l)
>       in FullLine ("The intruder guesses the value "++showMaths latex mstr)
>    "INTRUDER_M::verify" ->
>       let (v,g) = topLevel (msgpair latex) (dropFirstField l)
>       in FullLine ("The intruder verifies the guess of "++
>                    showMaths latex g++" using verifier "++showMaths latex v)
>    "close" ->
>	let id = getNthField 2 l
>	    role' = getNthField 3 l
>	    role = take (length role' - 1) role'
>	in  FullLine (showMaths latex id++" withdraws from this run as "++role)
>    "INTRUDER_M::spypick" ->
>      let (fresh,req,gen) = splitGeneration latex (dropFirstField l)
>      in FullLine (displayGeneration fresh req gen)
>    "_tau" -> None
>    "notknowit" -> None
>    "knowit" -> None
>    "deduce" -> None
>    "infer" -> None
>    "SECRET_M::scs"   -> None
>    "outofsteam" -> 
>	let t = getNthField 2 l
>	    t2 = take (length(t)-5) t
>	in FullLine
>	    ("The " ++ t2 ++ " Manager has run out of fresh values to" ++
>	    " supply to the network.  Declare one more variable as" ++
>	    " type " ++ t2 ++ "(Foreground) in #Actual Variables")
>    "error" -> None
>    _ -> error ("Unrecognized event: "++l)

>splitcomm latex l = 
>  let a = getFirstField l
>      b = (getFirstField . dropFirstField) l
>      n = (drop 3 . getFirstField . tl . dropFirstField . dropFirstField) l
>      m = (dropFirstField . dropFirstField . dropFirstField) l
>      mstr = topmsg latex m
>  in (a,b,n,mstr)

>splitGeneration latex l = 
>  let	ls = drop 1 l
>	f1 = if (take 1 ls == "(") then
>		  (drop 1 . takeWhile (/= ')')) ls
>	    else takeWhile (/= '>') ls
>	fresh = getAllFields(filter (notBracket) f1)
>	r1 = (drop 1 . takeWhile (/= '}') . dropWhile (/= '{')) ls
>	req = topmsgG latex r1
>	g1 = (takeWhile (/= '}') . drop 3 . dropWhile (/= '}')) ls
>	gen = topmsgG latex g1
>  in 
>	(fresh, req, gen)

>notBracket c = not(member c "()<>")

Produce output representing the spypick events.

>displayGeneration fresh req gen =
>  "The intruder performs the functionality of internal " ++
>  "process(es) and generates the set of messages {" ++ 
>  commaConcat gen ++ "} from the set of messages " ++
>  "(he knows) {" ++ commaConcat req ++ "} and the " ++
>  "fresh value(s) " ++ commaConcat fresh ++ " supplied."

Produce output representing intruder impersonating a

>mkIntruder False a = "I_"++a
>mkIntruder True a = "I_{"++a++"}"

====================================================================

Interpret line corresponding to signal event

>parseSignal :: Bool -> String -> String
>parseSignal latex l =
>  let ff = getFirstField l
>  in 
>  if ff == "Claim_Secret"
>  then 
>    let a = getNthField 2 l
>        s = getNthField 3 l
>        bs = (commaConcat . getAllFields . tl . dropNFields 3) l
>    in a++" believes "++showMaths latex s++" is a secret shared with "++bs
>  else if take 7 ff == "Running"
>  then 
>    let a = getNthField 3 l
>        r = (takeWhile (/= '_') . getNthField 2) l
>        b = getNthField 4 l
>        ds = getAllFields (dropNFields 4 l)
>    in a++" believes "++pronoun a++" is running the protocol, taking role "++
>       r++", with "++b++", using data items "++
>       commaConcat (map (showMaths latex) ds)
>  else if take 6 ff == "Commit"
>  then 
>    let a = getNthField 3 l
>        r = (takeWhile (/= '_') . getNthField 2) l
>        b = getNthField 4 l
>        ds = getAllFields (dropNFields 4 l)
>    in a++" believes "++pronoun a++
>       " has completed a run of the protocol, taking role "++r++
>       ", with "++b++", using data items "++
>       commaConcat (map (showMaths latex) ds)
>  else error ("unrecognized signal event"++l)

Produce text in maths mode if latex used

>showMaths True st = "$"++st++"$"
>showMaths False st = st

Gratuitous bit of code to try to use the correct pronouns

>pronoun "Alice" = "she"
>pronoun "Anne" = "she"
>pronoun "Bob" = "he"
>pronoun "Mallory" = "he"
>pronoun "Yves" = "he"
>pronoun "Ivo" = "he"
>pronoun "Sam" = "he"
>pronoun "Trent" = "he"
>pronoun "Jeeves" = "he"
>pronoun _ = "(s)he"

==================================================================

Parse message, and extras, returning appropriate string

>topmsg latex st = topLevel (msgextras latex) (init st)

Parse messages of the form Msg - used in the Generations set (spypick
events).  Similar to topMsg, except that it is not parsed the "extras"
field.

>topmsgG _ st = topLevel (listOf (msg False) ',') st

Parse extras, but ignore them

>msgextras latex = msg latex <^^ extras

Single message

>word_ :: Parse Char String
>word_ = 
>  spot isAlpha ^^^ many (spot isAlphanumor_) ^^^ many (token '\'') 
>    >>> (\ (c, (cs, ps)) -> remunderscore (c:cs++ps))
>  where isAlphanumor_ c = myisAlphanum c || c=='_'

>msg :: Bool -> Parse Char String
>msg latex =
>  word1 "Encrypt.(" ^^> msg latex ^^^ word1"," ^^> msgseq latex <^^ word1")" 
>     >>> (\ (k,ms) -> mkEncrypt latex ms k)
>  |||
>  word1 "Hash.(" ^^> word_ ^^^ word1 "," ^^> msgseq latex <^^ word1 ")" 
>    >>> (\ (h,ms) -> h++"("++commaConcat ms++")")
>  |||
>  word1 "Sq." ^^> msgseq latex >>> commaConcat
>  |||
>  word1 "Xor.(" ^^> msg latex ^^^ word1 "," ^^> msg latex <^^ word1 ")"
>    >>> (\ (m,m') -> m++mkXor latex++m')
>  |||
>  word1 "Timestamp." ^^> number >>> show
>  ||| 
>  fnappOrVar

>fnapp =
>   word_ ^^^ word1 "." ^^> arg >>> (\ (f,a) -> remunderscore f++"("++a++")")

>msgpair latex =
>  token '(' ^^> msg latex ^^^ token ',' ^^> msg latex <^^ token ')'

remove underscore from function name

>remunderscore f =
>  let l = length f 
>  in if l>2 && drop (l-2) f == "__" then take (l-2) f else f

>fnappOrVar = fnapp ||| word_

>extras :: Parse Char String
>extras = 
>  word1 ",<>" >>> (\_ -> "")
>  ||| extras1
>extras1 = 
>  word1 ",<" ^^> extra ^^^ extras2 >>> (\(e,es) -> "Extras: "++e++","++es)
>extras2 = 
>  word1 "," ^^> extra ^^^ extras2 >>> (\(e,es) -> e++","++es)
>  |||
>  word1 ">" >>> (\_ -> "")

>extra = 
>  word1 "Timestamp." ^^> number >>> show
>  |||
>  fnappOrVar

Sequence of messages between angle brackets

>msgseq, msgseq' :: Bool -> Parse Char [String]
>msgseq latex = word1 "<" ^^> msg latex ^^^ msgseq' latex >>> cons

>msgseq' latex =
>  word1 ">" >>> (\ _ -> [])
>  |||
>  word1 "," ^^> msg latex ^^^ msgseq' latex >>> cons

Argument of function

>arg :: Parse Char String
>arg = 
>  fnappOrVar
>  |||
>  word1 "(" ^^> fnappOrVar ^^^ arg' 
>    >>> (\ (w,ws) -> commaConcat (map remunderscore (w:ws)))

>arg' :: Parse Char [String]
>arg' =
>  word1 "," ^^> fnappOrVar ^^^ arg' >>> cons
>  |||
>  word1 ")" >>> (\_ -> [])

Functions to produce output, dependent on whether LaTeX is required

>mkEncrypt False ms k = "{"++commaConcat ms++"}{"++k++"}"
>mkEncrypt True ms k = "\\encrypt{"++commaConcat ms++"}{"++k++"}"
>mkXor False = " (+) "
>mkXor True = " \\oplus "

=========================================================================

Produce actual output


>showOutput :: Bool -> [Event] -> String
>showOutput latex es =
>  let nwidth = maximum [length n | Comm n _ _ _ <- es]
>      awidth = maximum [length a | Comm _ a _ _ <- es]
>      bwidth = maximum [length b | Comm _ _ b _ <- es]
>  in 
>  (if latex then "\\begin{protdesc}\n" else "")++
>  concat (map (showEvent latex nwidth awidth bwidth) es)++
>  (if latex then "\\end{protdesc}\n" else "")

Produce output for particular event

>showEvent :: Bool -> Int -> Int -> Int -> Event -> String
>showEvent True nw aw bw (Comm n a b m) = 
>  rjustify nw n++". & "++cjustify aw a++" & "++cjustify bw b++" & "++
>  m++" \\\\\n"
>showEvent False nw aw bw (Comm n a b m) = 
>  rjustify nw n++". "++cjustify aw a++" -> "++cjustify bw b++" : "++
>  m++"\n"
>showEvent True _ _ _ (FullLine st) = "\\fullline{"++st++"} \\\\\n"
>showEvent False _ _ _ (FullLine st) = "  "++st++"\n"
>showEvent _ _ _ _ None = ""

Pretty printing functions

>rjustify n st = spaces (n-length st)++st
>cjustify n st = 
>  let lpad = (n-length st) `div` 2
>  in spaces lpad++st++spaces (n-length st-lpad)


