Parser for protocol description part of file

>module Parse1 (parseFVars, getvars, getactvars, getinv, parseProcsInfo, 
>               parseProtDesc, parseSpecs) 
>where

>import Useful
>import Maybe1
>import Atoms
>import Messages
>import Types
>import GenParse
>import MiscParse
>import Msgparse

>type FnType1 = ([TypeName], TypeName)
>type FnTypeList1 = [(VarName, FnType1)]

==========================================================================
Variable parsing function: used in #FreeVariables section.

>getvars :: Line -> Maybe_ [(VarName, TypeType, [Subtype])]
>getvars = topLevel1 varTypeList "Error in free variable definition:"

>varTypeList :: Parse Char [(VarName, TypeType, [Subtype])]
>varTypeList = 
>  word ^^^ varTypeList' >>> (\ (v, (vs, t, st)) -> (v, t, st) : [(v',t, st) | v' <- vs])

>varTypeList' = 
>  tokenws ',' ^^> word ^^^ varTypeList' >>> (\ (v, (vs, t, st)) -> (v:vs, t, st))
>  |||
>  tokenws ':' ^^> varTypeList'' >>> (\ (t, st) -> ([], t, st))

>varTypeList'' :: Parse Char (TypeType, [Subtype])
>varTypeList'' = 
>  word ^^^ varTypeList''' 
>     >>> (\ (argt, (argts, rant)) -> (FnType (argt:argts) rant, []))
>  |||
>  wordws ^^^ subTypeVarList >>> (\ (t, sts ) -> (AtomType t, map (\st ->t++"_"++st) sts))
>  ||| wordws >>> (\t -> (AtomType t, []))

Parse a string of the form [Init, Resp] and returns ["Init"] ["Resp"]

>subTypeVarList :: Parse Char [String]
>subTypeVarList =
>   tokenws '[' ^^> subTypeVarList' <^^ tokenws ']' >>> id

>subTypeVarList' :: Parse Char [String]
>subTypeVarList' =
>   word ^^^ (token ',' ^^> subTypeVarList') >>> (\ (s, st) -> s:st)
>   ||| wordws >>> (\st -> [st])

>varTypeList''' :: Parse Char ([TypeName], TypeName)
>varTypeList''' =
>  cartprod ^^> wordws ^^^ varTypeList''' 
>     >>> (\ (argt, (argts, rant)) -> (argt:argts, rant))
>  |||
>  word1ws "->" ^^> wordws >>> (\ t -> ([], t))

Symbol representing cartesian product: either "x" or ","

>cartprod = 
>  white ^^> word1 "x" <^^ token ' ' 
 
Inverse lists

>getinv :: [Line] -> Maybe_ InverseKeyList
>getinv [] = Yes []
>getinv [l0] = topLevel1 parseinv "Error in inverse key list: " l0
>getinv _ = Error ("Error: multiple inverse key lists found\n")

>parseinv = 
>  word1ws "InverseKeys" ^^> tokenws '=' ^^> listOf keypair ','

>keypair = tokenws '(' ^^> wordws ^^^ tokenws ',' ^^> wordws <^^ tokenws ')'

==========================================================================
Variable parsing function used in #ActualVariables section


>getactvars :: Line -> Maybe_ [(VarName, TypeType, Status, [Subtype])]
>getactvars = topLevel1 actvarTypeList "Error in actual variable definition:"

>state "Normal" = Normal
>state "External" = External
>state "InternalUnknown" = InternalUnknown
>state "InternalKnown" = InternalKnown
>state _ = Error_Status

>actvarTypeList :: Parse Char [(VarName, TypeType, Status, [Subtype])]
>actvarTypeList = 
>  (wordws ^^^ many(tokenws ',' ^^> wordws) ^^^ tokenws ':'
>			^^> actvarTypeList'') 
>	>>> (\(w,(ws,(t,s, st))) -> [(w',t,s, st) | w'<- (w:ws)])

We assume that if a variable is in no subtype then it is in every subtype.

>actvarTypeList'' :: Parse Char (TypeType, Status, [Subtype])
>actvarTypeList'' = 
>  word ^^^ actvarTypeList''' 
>     >>> (\ (argt, (argts, rant)) -> (FnType (argt:argts) rant, Normal, []))
>  |||
>  (wordws ^^^ tokenws '(' ^^> wordws <^^ tokenws ')') ^^^ (subTypeVarList ||| succeed [])
>	  >>> (\((w, s), sts) -> (AtomType w, state s, map (\st -> w++"_"++st) sts))
>  |||
>  wordws >>> (\t -> (AtomType t, Normal, []))

>actvarTypeList''' :: Parse Char ([TypeName], TypeName)
>actvarTypeList''' =
>  cartprod ^^> wordws ^^^ actvarTypeList''' 
>     >>> (\ (argt, (argts, rant)) -> (argt:argts, rant))
>  |||
>  word1ws "->" ^^> wordws >>> (\ t -> ([], t))

==========================================================================
Parse #FreeVariables section

>parseFVars :: 
>  [Line] -> Maybe_ (VarTypeList, FnTypeList1, InverseKeyList, [DataTypeDef])
>parseFVars ls = 
>  let -- variable and function declarations
>      isdec l = take 11 l /= "InverseKeys" && take 8 l /= "datatype"
>      ls' = filter isdec ls 
>      maybevars1 = concat @@ combineMaybes (map getvars ls')
>      maybevars = (\ l -> [(v,t, st) | (v, AtomType t, st) <- l]) @@ maybevars1
>      maybefns = (\ l -> [(v,(ats,rant)) | (v, FnType ats rant, st) <- l]) 
>                 @@ maybevars1
>      -- inverse keys
>      ikls = filter ((== "InverseKeys") . take 11) ls
>      maybeinv = getinv ikls
>      maybeinv' = 
>        case maybeinv of
>          Error e -> Error e
>          Yes [] -> Error ("Error: no inverse key list found" ++ "\n")
>          Yes l -> Yes l
>      -- datatype definitions ...
>      dtls = filter ((== "datatype") . take 8) ls
>      maybedts = combineMaybes (map parseDtypeDef dtls)
> in (\ (((vl, fl), il), dt) -> (vl, fl, il, dt)) @@ 
>      (((maybevars &&& maybefns) &&& maybeinv') &&& maybedts)

>parseDtypeDef = topLevel1 dtypedef "Parse error in datatype definition:"

>dtypedef :: Parse Char DataTypeDef
>dtypedef = 
>  word1 "datatype" ^^> wordws ^^^ word1ws "=" ^^> pattern ^^^ dtypedef1
>  >>> (\(name, (p1, (ps, n))) -> (name, p1:ps, n))

>dtypedef1 = 
>  word1ws "|" ^^> pattern ^^^ dtypedef1 >>> (\(p,(ps,n)) -> (p:ps,n))
>  |||
>  word1ws "unwinding" ^^> number >>> (\n -> ([],n))

>pattern = 
>  wordws ^^^ word1ws "(" ^^> listOf wordws ',' <^^ word1ws ")" 
>  |||
>  wordws >>> (\w -> (w,[]))


==========================================================================
Parse #Processes section

>parseProcsInfo :: [Line] -> Maybe_ ProcessList
>parseProcsInfo ls = combineMaybes (map parseProcLine ls)

>parseProcLine :: Line -> Maybe_ ProcessInfo
>parseProcLine = topLevel1 procLine "Parse error in process definition line:"

procLine ::= procname "(" comma_list ")" ["knows" comma_list]

>--procLine :: Parse Char ProcessInfo
>procLine = 
>  ws word ^^^ tokenws '(' ^^> (termed_comma_list ')') ^^^ know ^^^ generate
>  >>> (\ (procname, (args, (knows,generates))) 
>			-> (hd args,procname,args,knows,generates))

>know :: Parse Char [Msg]
>know =
>  ws (word1 "knows") ^^> knowsList
>  ||| 
>  succeed []

>generate :: Parse Char [String]
>generate =
>  ws (word1 "generates") ^^> listOf wordws ','
>  ||| 
>  succeed []

>knowsItem = 
>  word ^^^ tokenws '(' ^^> termed_comma_list ')'  >>> mkfnapp
>  ||| 
>  word >>> Atom
>  where mkfnapp (f, as) =
>           if length as == 1 then Apply f (Atom (hd as))
>           else  Apply f (Sq (map Atom as))

>knowsList :: Parse Char [Msg]
>knowsList = knowsItem ^^^ knowsList' >>> (\ (v, vs) -> v:vs)

>knowsList' = 
>  tokenws ',' ^^> knowsItem ^^^ knowsList' >>> (\ (v, vs) -> v:vs)
>  |||
>  succeed []

==========================================================================
Parse #Protocol description section

>parseProtDesc :: [Line] -> Maybe_ ProtDesc
>parseProtDesc ls
>  | isError msteps   = Error (errorMsg msteps)
>  | otherwise        = combineMaybes (map parseProtStep (body msteps))
>  where msteps = splitpd ls

Split protocol description into (assignments, msg, tests) triples

>splitpd :: [Line] -> Maybe_ [(Line, Line, Line)]
>splitpd []     = Yes []
>splitpd (l:ls) 
>  | isAssignment l  = splitpd1 l ls
>  | otherwise       = splitpd1 "<>" (l:ls)

Split protocol description, giving first step assignment ass

>splitpd1 _ []         = Error "Bad protocol description\n"
>splitpd1 ass [l]        = Yes [(ass,l,"[]")]
>splitpd1 ass (l1:l2:ls) 
>  | isTest l2   = (\o -> (ass,l1,l2) : o) @@ splitpd ls
>  | otherwise   = (\o -> (ass,l1,"[]") : o) @@ splitpd (l2:ls)

>isAssignment l = hd (tokenize l) == "<"
>isTest l       = hd (tokenize l) == "["

Parse single step of protocol

>parseProtStep :: (Line, Line, Line) -> Maybe_ ProtMsgDesc
>parseProtStep (assm, msg, testm) = 
>  (\ (((n,a,b,m),testo),asso) -> (asso, n, a, b, m, testo)) 
>  @@ (parseMsg msg (tokenize msg) &&& parseTest testm &&& parseAss assm)

Parsing of assignments; strip off surrounding "<" and ">" first, in case of
embedded ">" characters

>parseAss :: Line -> Maybe_ AssignmentList
>parseAss assm = 
>  if head rest1 == '<' && head rest2 == '>' 
>  then topLevel1 assigns "Error in assignment: " rest3
>  else Error ("Error in assignment: " ++ assm++"\n")
>  where rest1 = dropWhite assm
>        rest2 = dropWhite (reverse (tail rest1))
>        rest3 = reverse (tail rest2) -- assignment without < and >

>assigns :: Parse Char [(VarName, String)]
>assigns = listOf assign ';' ||| succeed []

>assign :: Parse Char (VarName, String)
>assign = ws word ^^^ word1ws ":=" ^^> many (spot (/= ';'))

Parse message

>parseMsg :: Line -> [String] -> Maybe_ (MsgNo, Player, Player, Msg)
>parseMsg msg (n : "." : a : "-" : ">" : b : ":" : ms) = 
>  (\o -> (n, Agent a, Agent b, o)) @@ parseFields msg ms
>parseMsg msg (n : "." : "-" : ">" : b : ":" : ms) = 
>  (\o -> (n, Environment, Agent b, o)) @@ parseFields msg ms
>parseMsg msg (n : "." : a : "-" : ">" : ":" : ms) = 
>  (\o -> (n, Agent a, Environment, o)) @@ parseFields msg ms
>parseMsg msg _ = 
>  Error ("Bad protocol step: " ++ msg ++ "\n")

>parseFields :: Line -> [String] -> Maybe_ Msg
>parseFields l ts = 
>  case parsemsg (concat ts) of  
>      Just (result,[]) -> Yes result
>      _ -> Error ("parse unsuccessful: " ++ l ++ "\n")

Parse test

>parseTest :: Line -> Maybe_ Test
>parseTest testm
>  | test1 /= [] && hd test1 == '[' && rest == "]"  
>                = Yes (test2, any (=="now") (tokenize testm))
>  | otherwise   = Error ("Bad test: " ++ testm)
>  where test1 = dropWhile isWhite testm
>        test2 = takeWhile (/= ']') (tl test1)
>        rest  = dropWhite (dropWhile (/= ']') test1)

==========================================================================
Parse #Specification section

>parseSpecs :: [Line] -> Maybe_ ((Secrets, Auths), [TemporalLogicSpec])
>parseSpecs ls = msecrets &&& mauths &&& mTemporalSpecs
>  where ltss = [(l, tokenize l) | l <- ls]
>        msecrets = 
>          combineMaybes 
>            [parseSecret l ts | (l, sl : ts) <- ltss, member sl secLabels]
>        mauths = 
>          combineMaybes 
>            [parseAuth l (t:ts) | (l, t:ts) <- ltss, member t authLabels]
>        mTemporalSpecs =
>           combineMaybes
>               [parseTemporalSpec l | (l, t:_) <- ltss, not (member t specLabels)]
>        authLabels = 
>          ["Aliveness", "WeakAgreement", "NonInjectiveAgreement", 
>           "Agreement",
>	        "TimedAliveness", "TimedWeakAgreement", 
>           "TimedNonInjectiveAgreement", "TimedAgreement", 
>           "Authentication"]
>        secLabels = ["Secret", "StrongSecret"]
>        specLabels = secLabels++authLabels

Parse a temporal specification

>parseTemporalSpec :: Line -> Maybe_ TemporalLogicSpec
>parseTemporalSpec l = topLevel1 parseTemporalSpec1 "Bad temporal specification: " l

Parse an if expression, which takes up the whole line (note use of eol)

>parseTemporalSpec1 :: Parse Char TemporalLogicSpec
>parseTemporalSpec1 = 
>   word1ws "if" ^^> parseTemporalFormula ^^^ word1ws "then" ^^> parseTemporalFormula <^^ eol
>   >>> (\ (f1, f2) -> AlwaysIf f1 f2)

We rewrite the grammar as:
    B -> eB' | (B)B' | Prev B
    B' -> "and" B | "or" B | epsilon

>parseTemporalFormula :: Parse Char TLFormula
>parseTemporalFormula = 
>   ((tokenws '(' ^^> parseTemporalFormula <^^ tokenws ')') `into` parseTemporalFormula')
>   ||| (word1ws "previously" ^^> parseTemporalFormula >>> 
>           (\ f -> Previously f))
>   ||| (parseTemporalEvent `into` (\ e -> parseTemporalFormula' (Does e)))

>parseTemporalFormula' :: TLFormula -> Parse Char TLFormula
>parseTemporalFormula' f1 = 
>   (word1ws "and" ^^> parseTemporalFormula >>> (\ f2 -> And f1 f2))
>   ||| (word1ws "or" ^^> parseTemporalFormula >>> (\ f2 -> Or f1 f2))
>   -- If the other ones have failed then we assume that there is no other
>   -- statement on this line (if an error was there then eol would detect it as
>   -- not all the input would have been consumed).
>   ||| succeed f1

Parse a single TLEvent string

>parseTemporalEvent :: Parse Char TLEvent
>parseTemporalEvent = 
>   wordws ^^^ (msgIdRecipientParser "sends" "to" ||| msgIdRecipientParser "receives" "from") 
>   ^^^ optional1 (word1ws "containing" ^^> listOf substitution ',') []
>   >>> (\ (agentId, ((sendReceives, (messageId, otherAgentId)), boundVars)) ->
>           (agentId,otherAgentId,parity sendReceives,messageId,boundVars))
>   where
>       substitution = 
>           wordws ^^^ word1ws "for" ^^> wordws >>> (\ (x,y) -> Substitution y x)
>           ||| wordws >>> (\ x -> FreeVar x)
>       msgIdRecipientParser x y = 
>           word1ws x ^^^ word1ws "message" ^^> dwordws 
>           ^^^ optional1 (word1ws y ^^> wordws) ""
>       parity "sends" = Send
>       parity "receives" = Receive

Parse secrets

>parseSecret l _ = topLevel1 parseSecret1 "Bad secret specification: " l

>parseSecret1 :: Parse Char Secret
>parseSecret1 =
>  word1ws "Secret" ^^> parseSecret2 
>    >>> (\ (a, (s, ts)) -> Sec a s ts)
>  |||
>  word1ws "StrongSecret" ^^> parseSecret2 
>    >>> (\ (a, (s, ts)) -> StrongSec a s ts)

>parseSecret2 :: Parse Char (AgentId, (Msg, [AgentId]))
>parseSecret2 =
>  tokenws '(' ^^> ws word ^^^ tokenws ',' ^^> 
>    ws cpt ^^^ tokenws ',' ^^>
>    tokenws '[' ^^> termed_comma_list ']' <^^ tokenws ')'

Parse authentication specs

>parseAuth _ ("Authentication" : _) =
>  Error ("The \"Authentication\" specification has been removed; " ++
>         "I suggest you use \"Agreement\" instead\n")
>parseAuth _ ["Aliveness", "(", a, ",", b, ")"] =
>  Yes (a, b, Aliveness)
>parseAuth _ ["WeakAgreement", "(", a, ",", b, ")"] =
>  Yes (a, b, WeakAgreement)
>parseAuth l ("NonInjectiveAgreement" : "(" : a : "," : b : "," : "[" : ts) =
>  (\ (ds,_) -> (a, b, NonInjectiveAgreement ds)) @@
>    checkM (parseCommaList l "]" ts)
>           (\(_,rest) -> rest == [")"],
>            "Bad authentication specification: " ++ l ++ "\n")
>parseAuth l ("Agreement" : "(" : a : "," : b : "," : "[" : ts) =
>  (\ (ds,_) -> (a, b, Agreement ds)) @@
>    checkM (parseCommaList l "]" ts)
>           (\(_,rest) -> rest == [")"],
>            "Bad authentication specification: " ++ l ++ "\n")
>parseAuth _ ["TimedAliveness", "(", a, ",", b, ",", t, ")"] | isNum t =
>  Yes (a, b, TimedAliveness (parseInt t))
>parseAuth _ ["TimedWeakAgreement", "(", a, ",", b, ",", t, ")"] | isNum t =
>  Yes (a, b, TimedWeakAgreement (parseInt t))
>parseAuth l ("TimedNonInjectiveAgreement":"(":a:",":b:",":t:",":"[":ts)
>  | isNum t  =
>  (\ (ds,_) -> (a, b, TimedNonInjectiveAgreement (parseInt t) ds)) @@
>    checkM (parseCommaList l "]" ts)
>           (\(_,rest) -> rest == [")"],
>            "Bad authentication specification: " ++ l ++ "\n")
>parseAuth l ("TimedAgreement":"(":a:",":b:",":t:",":"[":dts) | isNum t =
>  (\ (ds,_) -> (a, b, TimedAgreement (parseInt t) ds)) @@
>    checkM (parseCommaList l "]" dts)
>           (\(_,rest) -> rest == [")"],
>            "Bad authentication specification: " ++ l ++ "\n")
>parseAuth l _ = Error ("Bad authentication specification: " ++ l ++ "\n")

