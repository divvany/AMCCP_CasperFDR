Parser, to take string representing file, and return corresponding
representation of protocol, of type PreInput

>module Parse (parse) where

>import Useful
>import Maybe1
>import Pprint
>import Atoms
>import Messages
>import Types
>import GenParse
>import MiscParse
>import Msgparse
>import Parse1

>import List

==========================================================================

The main parsing function

>parse :: String -> Maybe_ Input
>parse file = 
>  let sects = (map (\(s,ls) -> (getKeyword s, ls)) . split . 
>               filter (not . comment) . makeLogicalLines . lines)
>                  file
>      badKWerrs =
>        ["Unrecognized keyword: " ++ st ++ "\n" | (None st,_) <- sects]
>      duplicates [] = []
>      duplicates (kw : kws) 
>        | member kw kws      = kw : duplicates kws
>        | otherwise          = duplicates kws
>      duplicateKWerrs = 
>       ["Duplicated keyword: " ++ show kw ++ "\n" | 
>           kw <- duplicates (map fst sects)]
>      warnings = concat (badKWerrs ++ duplicateKWerrs)
>  in 
>  if warnings /= "" then Error warnings 
>  else
>  let mfvinfo = parseFVars (select FreeVars sects)
>      mprocs = parseProcsInfo (select Processes sects)
>      mprotdesc = parseProtDesc (select ProtDesc sects)
>      mspecs = parseSpecs (select Specs sects)
>      mvinfo = parseVars (select ActualVars sects)
>      minlines = parseFunctions (select Inlines sects)
>      mactAgents = parseActualAgents (select System sects)
>      mintInfo = parseIntruderDef (select IntruderInf sects)
>      mequivs = parseEquivs (select Equivs sects)
>      (mchannels, mnewchannels, msessinfo) = parseChannels (select Channels sects)
>--      mnewchannels = parseNewChannels (select Channels sects)
>      output1 = 
>         (mfvinfo &&& mprocs &&& mprotdesc &&& mspecs &&& mvinfo &&& 
>          minlines &&& mactAgents &&& mintInfo &&& mequivs &&& mchannels)
>  in 
>  if isError output1 then (let Error e = output1 in Error e) 
>                          -- type coercion hack
>  else
>  let Yes (fvts,fnts,fiks,dtdefs) = mfvinfo
>      Yes procs = mprocs
>      Yes protdesc = mprotdesc
>      Yes ((secrets,auths),temporalSpecs) = mspecs
>      Yes (vts,iks,tsinfo) = mvinfo
>      Yes inlines = minlines
>      Yes ((actAgents,withdraw),generatesystem) = mactAgents
>      fnts' = [(f, if member (Symbolic f) inlines then Symb dts rt 
>                   else Defed dts rt) | 
>                 (f,(dts,rt)) <- fnts] ++
>              [(f, HashFunction) | (f,t,_) <- fvts, t=="HashFunction"] ++
>              -- Turn datatype constructors into functions:
>              [(cons, Symb args tn) | 
>                 (tn,pats,_) <- dtdefs, (cons, args) <- pats, args/=[]]
>      fvts' = [(f, t, st) | (f, t, st) <- fvts, t /= "HashFunction"] ++
>              -- turn datatype constructors with no arguments into variables:
>              [(cons, tn, []) | (tn,pats,_) <- dtdefs, (cons, []) <- pats]
>      Yes ((((((intruderId,ik0),intruderProcs),crackables),deductions),
>             guessables),unboundpar) = mintInfo
>      Yes equivs = mequivs
>      Yes channels = mchannels
>      Yes newchannels = mnewchannels
>      Yes sessinfo = msessinfo
>  in Yes (fvts', fnts', fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>          vts, iks, tsinfo, inlines, actAgents, withdraw, unboundpar, 
>          generatesystem, intruderId, ik0, 
>          intruderProcs, crackables, deductions, guessables, equivs, channels, 
>          newchannels, sessinfo)

========================================================================
Recognize section headers, and convert into keywords

>data Keyword = FreeVars | Processes | ProtDesc | Specs | ActualVars |
>               Inlines | System | IntruderInf | Equivs | Channels |
>               Preamble | None String
>               deriving (Eq, Show)

>getKeyword :: Line -> Keyword
>getKeyword "#Preamble" = Preamble
>getKeyword "#Freevariables" = FreeVars
>getKeyword "#Processes" = Processes
>getKeyword "#Protocoldescription" = ProtDesc
>getKeyword "#Specification" = Specs
>getKeyword "#Actualvariables" = ActualVars
>getKeyword "#Inlinefunctions" = Inlines
>getKeyword "#Functions" = Inlines
>getKeyword "#System" = System
>getKeyword "#IntruderInformation" = IntruderInf
>getKeyword "#Equivalences" = Equivs
>getKeyword "#Channels" = Channels
>getKeyword other = None other

==========================================================================
Parse #ActualVariables section

>parseVars :: [Line] -> Maybe_ (ActVarTypeList, InverseKeyList, TimeStampInfo)
>parseVars ls = 
>  let	ls' = map dropWhite ls
>	ls'' = -- lines with variable declarations
>              [l | l <- ls', -- tok = hd(tokenize l),
>                  hd(tokenize l) /= "InverseKeys" 
>                  && hd(tokenize l) /= "TimeStamp" 
>                  && hd(tokenize l) /= "MaxRunTime"]
>	ikls = [l | l <- ls', take 11 l == "InverseKeys"]
>	tsls = [(l, tokenize l) | l <- ls', take 9 l == "TimeStamp"]
>	rtls = [(l, tokenize l) | l <- ls', take 10 l == "MaxRunTime"]
>	maybevars = concat @@ 
>                  combineMaybes 
>                    [(combineMaybes . map checkVar) ## getactvars l | l <- ls'']
>	checkVar (v, AtomType t, s, st) = 
>		case s of
>		 Error_Status -> Error "Unknown Type Status"
>		 _ -> Yes (v, t, s, st)
>	checkVar (_, FnType _ _, _, _) = Error "Unexpected function declaration in #ActualVariables section\n"
>  in
>  (\ ((vl,il),tsi) -> (vl,il,tsi)) @@ 
>     ((maybevars &&& getinv ikls) &&& gettsinfo tsls rtls)
>    

Time stamp definition

>gettsinfo :: [(Line, [String])] -> [(Line, [String])] -> Maybe_ TimeStampInfo
>gettsinfo [] [] = Yes NotUsed
>gettsinfo [] rtls = (\rt -> MRTUsed rt) @@ getrt rtls
> -- Error "Unnecessary MaxRunTime definition.\n"
>gettsinfo [(_, ["TimeStamp", "=", t0, ".", ".", t1])] rtls 
>  | isNum t0 && isNum t1 
>     = (\rt -> TimeStampsUsed (parseInt t0) (parseInt t1) rt) @@ getrt rtls
>gettsinfo [(l,_)] _ = Error ("Bad TimeStamp definition: "++l++"\n")
>gettsinfo _ _ = Error ("Multiple TimeStamp definitions\n")

>getrt :: [(Line, [String])] -> Maybe_ Int
>getrt [] = Error "No MaxRunTime definition"
>getrt [(_, ["MaxRunTime", "=", rt])] | isNum rt = Yes (parseInt rt)
>getrt [(l,_)] = Error ("Bad MaxRunTime definition: "++l++"\n")
>getrt _ = Error ("Multiple MaxRunTime definitions\n")




==========================================================================
Parse #Functions section

>parseFunctions :: [Line] -> Maybe_ [Function]
>parseFunctions ls = concat @@ (combineMaybes (map parseFunction ls))

>parseFunction :: Line -> Maybe_ [Function]
>parseFunction = topLevel1 function "Parse error in function definition:"


inline ::= fnname "(" comma_list ")" "=" inlineRHS | symbolic comma_list
inlineRHS ::= varname -- only atoms at present

>function :: Parse Char [Function]
>function = 
>  word1ws "symbolic" ^^> comma_list >>> (\ fs -> map Symbolic fs)
>  |||
>  word1ws "inline" ^^> functionLHS ^^^ tokenws '=' ^^> many anyc
>    >>> (\ ((f, as), rhs) -> [Inline (f, as, rhs)])
>  |||
>  functionLHS ^^^ tokenws '=' ^^> fnRHS
>    >>> (\ ((f, as), rhs) -> [Defined (f, as, rhs)])

>anyc = spot (\ _ -> True)

>functionLHS = word ^^^ tokenws '(' ^^> fn_args

>fn_args :: Parse Char [String]
>fn_args = listOf fn_arg ',' <^^ tokenws ')'

>fn_arg = wordws ||| word1ws "_"

>fnRHS :: Parse Char FunctionRHS
>fnRHS = wordws

fn_arg ^^^ fn_args' >>> cons 
fn_args' =
  tokenws ',' ^^> fn_arg ^^^ fn_args' >>> cons
  |||
  tokenws ')' >>> (\ _ -> []) -}

==========================================================================

Parse #System section

*** Rewrite to parse sequential compositions

>parseActualAgents :: [Line] -> Maybe_ ((ActualAgents, Bool), GenerateSystem)
>parseActualAgents ls =
>   let	
>       ls'  = ls
>       wdls = [l | l<-ls', hd(tokenize l)=="WithdrawOption"]
>       wdres = if length(wdls)==1 then withdrawOption (hd(wdls))
>           else if (wdls == []) then Yes False
>           else Error "Multiple Withdraw Options Defined."
>       generateSystem =
>           if length (generateSystemForRepeatLs) == 1 then repeatSystem (hd (generateSystemForRepeatLs))
>           else if length(generateSystemLs) == 1 then generatesystem(hd(generateSystemLs))
>           else if generateSystemLs == [] && generateSystemForRepeatLs == [] then Yes DontGenerate
>           else Error "Multiple generate system options defined"
>       generateSystemLs = [l | l<-ls', hd(tokenize l)=="GenerateSystem"]
>       generateSystemForRepeatLs = [l | l<-ls', hd(tokenize l)=="GenerateSystemForRepeatSection"]
>       ls'' = [l | l<-ls', hd(tokenize l)/="WithdrawOption" 
>                           && hd(tokenize l)/="GenerateSystem"
>                           && hd (tokenize l) /= "GenerateSystemForRepeatSection"]
>   in
>       parseActualAgents1 ls'' &&& wdres &&& generateSystem

>parseActualAgents1 :: [Line] -> Maybe_ ActualAgents
>parseActualAgents1 ls = 
>	combineMaybes (map parseAgent ls)

>parseAgent = topLevel1 parseAgent1 "Bad agent specification"

Parse possibly sequential agent, eg:

  INITIATOR(Alice, Na1) ; INITIATOR(Alice, Na2)

or starred form, eg:

  INITIATOR(Alice, Na) *

>parseAgent1 :: Parse Char SeqActualAgent
>parseAgent1 = 
>  parseOneAgent <^^ word1ws "*" >>> (\p -> Star p)
>  |||
>  listOf (ws parseOneAgent) ';' >>> (\ps -> SeqComp ps)

parse single instance of agent (eg "INITIATOR(Alice, Na)")

>parseOneAgent :: Parse Char ActualAgent
>parseOneAgent = word ^^^ token '(' ^^> termed_comma_list ')'

>withdrawOption :: Line -> Maybe_ Bool
>withdrawOption = 
>  topLevel1 withdrawOption1 "Error in Withdraw Option:"

>withdrawOption1 :: Parse Char Bool
>withdrawOption1 = 
>  word1ws "WithdrawOption" ^^> word1ws "=" ^^> 
>  ((word1ws "True" >>> \_ -> True)
>  |||
>  (word1ws "False" >>> \_ -> False))

==========================================================================
Parse definition of intruder

intruderDef ::= intruderId intruderKnowledge
                [processInfo] [crackableInfo] [deductions]

>parseIntruderDef :: [Line] -> 
>			Maybe_ ((((((IntruderId,IntruderInitKnowledge), 
>				[ProcessName]),[CrackInfo]), 
>				[Deduction]), [TypeName]), Bool)
>parseIntruderDef (l:l':ls) = 
>  let
>	ls'  = map dropWhite ls
>	unparls = [l | l<-ls', hd(tokenize l)=="UnboundParallel"]
>	unparL = if length(unparls)==1
>		then
>			unboundParallel(hd(unparls))
>		else
>			if (unparls == [])
>			then
>				Yes False
>			else
>				Error "Multiple UnboundParallel Options Defined."
>	ls'' = [l | l<-ls', hd(tokenize l)/="UnboundParallel"]
>  in
>	intruderId l &&& intruderKnowledge l' &&& processInfo ls''
>	        &&& crackables ls'' &&& deductions ls'' &&& guessables ls'' &&& unparL

------------------ Unbound Parallel Sessions

>unboundParallel:: Line -> Maybe_ Bool
>unboundParallel= 
>  topLevel1 unboundParallel1 "Error in Unbound Parallel Flag:"

>unboundParallel1:: Parse Char Bool
>unboundParallel1 = 
>  word1ws "UnboundParallel" ^^> word1ws "=" ^^> 
>  ((word1 "True" >>> \_ -> True)
>  |||
>  (word1 "False" >>> \_ -> False))

>generatesystem :: Line -> Maybe_ GenerateSystem
>generatesystem= 
>  topLevel1 generatesystem1 "Error in generate system Flag:"

>generatesystem1:: Parse Char GenerateSystem
>generatesystem1 = 
>  word1ws "GenerateSystem" ^^> word1ws "=" ^^> 
>  ((word1 "True" >>> \_ -> GenerateStandard)
>  |||
>  (word1 "False" >>> \_ -> DontGenerate))

>repeatSystem :: Line -> Maybe_ GenerateSystem
>repeatSystem = topLevel1 p "Error in generate system for repeat flag:"
>   where
>       p = word1ws "GenerateSystemForRepeatSection" ^^> word1ws "=" 
>           ^^> dwordws ^^^ word1ws "to" ^^> dwordws
>           >>> (\ (from, to) -> GenerateRepeatSection from to)

------------------- Intruder's identity

IntruderId ::= "Intruder" "=" String

>intruderId :: Line -> Maybe_ IntruderId
>intruderId = 
>  topLevel1 intruderId1 "Error in intruder identity:"

>intruderId1 :: Parse Char IntruderId
>intruderId1 = 
>  word1 "Intruder" ^^> tokenws '=' ^^> wordws


----------------- Intruder's initial knowledge

intruderKnowledge  ::= "IntruderKnowledge" "=" "{" String intruderKnowledge'
intruderKnowledge' ::= [, String] "}"

>intruderKnowledge :: Line -> Maybe_ IntruderInitKnowledge
>intruderKnowledge = 
>  topLevel1 intruderKnowledge1 "Error in intruder knowledge:"

>intruderKnowledge1 :: Parse Char IntruderInitKnowledge
>intruderKnowledge1 =
>  word1 "IntruderKnowledge" ^^> tokenws '=' ^^> tokenws '{' 
>    ^^> intuderKnowledgeDatum ^^^ intruderKnowledge2
>  >>> cons
>  -- (\ (m, ms) -> m:ms)

>intruderKnowledge2 =
>  tokenws ',' ^^> intuderKnowledgeDatum ^^^ intruderKnowledge2 
>     >>> cons
>  |||
>  tokenws '}' >>> (\ _ -> [])

>intuderKnowledgeDatum :: Parse Char Msg
>intuderKnowledgeDatum = cpt -- fnappOrVar

--------------- Processes to be incorporated into the intruder

>processInfo :: [Line] -> Maybe_ [ProcessName]
>processInfo ls = 
>  let	ls'  = map dropWhite ls
>	ls'' = [l | l<-ls', hd(tokenize l)=="IntruderProcesses"]
>	ls'''= if (ls'' == []) then [] else hd(ls'')
>  in
>	intruderProcesses (ls''')

>intruderProcesses :: Line -> Maybe_ [ProcessName]
>intruderProcesses = 
>  topLevel1 intruderProcesses1 "Error in IntruderProcesses:"

>intruderProcesses1 :: Parse Char [ProcessName]
>intruderProcesses1 =
>  word1 "IntruderProcesses" ^^> tokenws '=' 
>    ^^> wordws ^^^ intruderProcesses2
>  >>> cons
>  |||
>  succeed []

>intruderProcesses2 =
>  tokenws ',' ^^> wordws ^^^ intruderProcesses2 
>     >>> cons
>  |||
>  succeed []

------------ Types crackable by intruder

>crackables :: [Line] -> Maybe_ [CrackInfo]
>crackables ls = 
>  let	ls' = [l | l<-ls, hd(tokenize l)=="Crackable"]
>  in if ls'==[] then Yes [] else crackables2 (hd ls')

>crackables2 = topLevel1 crackables3 "Error in crackables"

>crackables3 = word1 "Crackable" ^^> tokenws '=' ^^> listOf crackItem ','

>crackItem :: Parse Char CrackInfo
>crackItem = wordws ^^^ crackTime

>crackTime :: Parse Char (Maybe Int)
>crackTime = 
>  word1ws "(" ^^> number <^^ word1ws ")" >>> Just
>  ||| succeed Nothing

--------------- Guessable values

>guessables :: [Line] -> Maybe_ [TypeName]
>guessables ls = 
>  let	ls' = [l | l<-ls, hd(tokenize l)=="Guessable"]
>  in if ls'==[] then Yes [] else guessable2 (hd ls')

>guessable2 = topLevel1 guessable3 "Error in guessables"

>guessable3 = word1 "Guessable" ^^> tokenws '=' ^^> listOf wordws ','

--------------- Extra deductions of form

Parse deductions such as "forall ka, kb : Key . ka, {kb}{Ks} |- {kb}{ka}"

deduction ::= "forall" quants Msg ["," Msg] "|-" Msg

>deductions :: [Line] -> Maybe_ [Deduction]
>deductions ls = 
>  let	ls' = map dropWhite ls
>	ls''= [l | l<-ls', 
>                  let w1 = hd(tokenize l) 
>                  in w1 `notElem` ["IntruderProcesses", "IntruderRoles", 
>                                   "Crackable", "Guessable"]]
>  in
>	combineMaybes (map deduction ls'')

>deduction = topLevel1 deduction1 "Error in deduction"

>deduction1 :: Parse Char Deduction
>deduction1 =
>  word1ws "forall" ^^> conds ^^^ parsemsg ^^^ deduction2
>    >>> (\ (qs, (m, (ms, m'))) -> (qs, flatten m++ms, m'))

>deduction2 :: Parse Char ([Msg], Msg)
>deduction2 = 
>  tokenws ',' ^^> parsemsg ^^^ deduction2 >>> 
>      (\ (m, (ms, m')) -> (flatten m++ms, m'))
>  |||
>  word1ws "|-" ^^> parsemsg >>> (\ m -> ([], m))

Flatten sequences, to recognize comma-separated messages in deductions as
individual messages, not sequences.

>flatten (Sq ms) = ms
>flatten m = [m]

Parse conditions

conds ::= cond [";" cond] "." 

>conds :: Parse Char [Cond]
>conds = cond ^^^ conds' >>> (\(c,cs) -> c++cs)

>conds' :: Parse Char [Cond]
>conds' =
>  word1ws ";" ^^> cond ^^^ conds' >>> (\(c,cs) -> c++cs)
>  |||
>  word1ws "." >>> (\_ -> [])

Parse condition, firstly storing result as Quant, then translating into
Cond:

cond = varName {, varName} [: typename1]

>type Quant = ([VarName], TypeName)
>quant2conds (vs,t) = [(v,t) | v <- vs]

>cond :: Parse Char [Cond]
>cond = 
>  word ^^^ cond' >>> (\ (v, (vs,typename)) -> quant2conds(v:vs, typename))

>cond' :: Parse Char Quant
>cond' = 
>  tokenws ',' ^^> word ^^^ cond' 
>    >>> (\ (v, (vs, typename)) -> (v:vs, typename))
>  |||
>  tokenws ':' ^^> typename1 >>> (\ typename -> ([], typename))
>  |||
>  succeed ([], "")

typename1 ::= "Message" | typename
The following parser could be simplified, but this makes it explicit that 
Message is distinguished.

>typename1 =
>  word1ws "Message" ||| word 

=============================================================
Parse equivalences

>parseEquivs :: [Line] -> Maybe_ [Equivalence]
>parseEquivs ls = combineMaybes (map equiv ls)

>equiv = topLevel1 equiv1 "Error in equivalence"

equiv1 ::= forall cond {; cond} "." Msg "=" Msg
 
>equiv1 :: Parse Char Equivalence
>equiv1 = 
>  word1ws "forall" ^^> conds ^^^ parsemsg ^^^ word1ws "=" ^^> parsemsg 
>    >>> (\ (cs, (m1, m2)) -> (cs, m1, m2))

==================================================================
Parse channel information

It would be better to return a Maybe_ of a triple.

>parseChannels :: [Line] -> (Maybe_ ChannelInfo, Maybe_ [NewChannelInfo], Maybe_ [SessionInfo])
>parseChannels [] = (Yes (Some [], Some [], Some []), Yes [], Yes [])
>parseChannels ls = -- parseChannels1 ls
>  let res = unzip3 @@ combineMaybes (map chan ls) 
>  in
>  if isError res then let Error e = res in (Error e, Error "", Error "") 
>  else let Yes (cs, ncs, sis) = res 
>       in (Yes (combineCIs cs), Yes (concat ncs), Yes (concat sis))

parseChannels1 ls = (Yes cs', Yes ncs', Yes sis')
  where Yes (cs, ncs, sis) = unzip3 @@ combineMaybes (map chan ls)
        cs' = combineCIs cs
        ncs' = concat ncs
        sis' = concat sis


>chan = topLevel1 (chan1 ||| sessinfo1 ||| newchan1) "Error in channel information"

>sessinfo1 :: Parse Char (ChannelInfo, [NewChannelInfo], [SessionInfo])
>sessinfo1 = sesstype >>> (\x -> ((Some [], Some [], Some []), [], [x]))

>sesstype = (word1ws "Stream" ^^> sessstrength 2) ||| (word1ws "Session" ^^> sessstrength 1)
>sessstrength x = (word1ws "symmetric" ^^> sessmsgs (x,2)) ||| (word1ws "injective" ^^> sessmsgs (x,1)) ||| sessmsgs (x,0)
>sessmsgs (x,y) = listOf dwordws ',' >>> (\z -> (x,y,z))

>newchan1 :: Parse Char (ChannelInfo, [NewChannelInfo], [SessionInfo])
>newchan1 = (dwordws ^^^ chanspec) >>> (\y -> ((Some [], Some [], Some []), [y], []))

>chanspec = (cchan ^^^ nfchan ^^^ nhchan ^^^ nrchan) >>> (\ (c,(nf,(nh,nr))) -> (c,nf,nh,nr))

>cchan = (word1ws "C" ^^> succeed 1) ||| (succeed 0)
>nfchan = (word1ws "NF" ^^> succeed 1) ||| (succeed 0)
>nhchan = (word1ws "NRA-" ^^> succeed 1) ||| (word1ws "NRA" ^^> succeed 2) ||| (succeed 0)
>nrchan = (word1ws "NR-" ^^> succeed 1) ||| (word1ws "NR" ^^> succeed 2) ||| (succeed 0)

>chan1 :: Parse Char (ChannelInfo, [NewChannelInfo], [SessionInfo])
>chan1 = 
>  (secretchan ||| authchan ||| directchan) >>> (\x -> (x, [], []))

Parse individual channel types

>secretchan =
>  word1ws "secret" ^^> (
>    listOf dwordws ',' >>> (\ xs -> (Some xs, Some[], Some[]))
>    |||
>    succeed (All, Some[], Some[])
>  )

>authchan = 
>  word1ws "authenticated" ^^> (
>    listOf dwordws ',' >>> (\ xs -> (Some[], Some xs, Some[]))
>    |||
>    succeed (Some [], All, Some [])
>  )

>directchan = 
>  word1ws "direct" ^^> (
>    listOf dwordws ',' >>> (\ xs -> (Some[], Some[], Some xs))
>    |||
>    succeed (Some[], Some[], All)
>  )

Combine list of ChannelInfo tuples into single tuple

>combineCIs = addDirect . foldr f (Some [],Some [],Some [])
>  where f (b1,b2,b3) (b1',b2',b3') = (combineCI b1 b1',
>                                      combineCI b2 b2',
>                                      combineCI b3 b3')
>        addDirect (b1,b2,b3) = (b1,b2,combineCI (combineCI b1 b2) b3)

>combineCI All _  = All
>combineCI _ All  = All
>combineCI (Some xs) (Some ys) = Some (union xs ys)
