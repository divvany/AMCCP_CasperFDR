Produce definitions of types, channels, etc

>module Channels(
>  typedefs, channeldefs, declareSignals, timingDefs) 
>where

>import Useful
>import Pprint
>import Types
>import Atoms
>import Annotated
>import Messages
>import SecureChannels

============================================================================
Produce definitions of main types, and a few useful functions

>typedefs :: Annotated -> Output
>typedefs an =
>  -- Encryption datatype 
>  encryption an ++
>  
>  ifFlagString an UnboundedParallel (
>    "-- Some indirection to get around FDR parsing bugs with :: in datatype declarations\n"++
>    nlConcat 0 ["AUTH"++show n++"_M__TaggedSignals"++show n
>                   ++" = AUTH"++show n++"_M::TaggedSignals"++show n
>               | (n,_,_) <- authinfo an]
>    ++ "\n\n"
>  )++
>  "-- All keys and hashfunctions in the system\n\n"++
>  "ALL_KEYS :: {Encryption}\n"++
>  "ALL_KEYS = " ++
>  (makeUnion 2 . remdups . map (findtype2 (fvts an) (fnts an)) . sortremdupsconcat)
>        [keys m | (_,_,_,_,m,_,_,_) <- protdesc an] ++
>  "\n" ++
>  "ASYMMETRIC_KEYS = {k_, inverse(k_) | k_ <- ALL_KEYS, k_!=inverse(k_)}\n"++
>  "HashFunction :: {Encryption}\n"++
>  "HashFunction = {"++commaConcat[f | (f, HashFunction) <- fnts an] ++ "}\n\n"++
>  "-- All atoms in the system\n\n"++
>  "ATOM = {" ++  format 9 ", " (remdups (actvtsnames an++ ["Garbage"]))
>  ++ "}\n\n" ++
>  -- type TS of timestamps (integers)
>  produceTimeInfo (timestampinfo an) ++
>  "-- Some standard functions\n\n"++
>  "channel dummyrun_\n"++
>  "RUN(X_) = \n"++
>  "  let drun = dummyrun_ -> drun\n"++
>  "  within drun[[dummyrun_ <- x_ | x_ <- X_]]\n\n"++
>  "encrypt(m_,k_) = Encrypt.(k_,m_)\n"++
>  "decrypt(Encrypt.(k1_,m_),k_) = if k_ == inverse(k1_) then m_ else <Garbage>\n"++
>  "decrypt(_,_) = <Garbage>\n"++
>  "decryptable(Encrypt.(k1_,m_),k_) = k_ == inverse(k1_) \n"++
>  "decryptable(_,_) = false\n"++
>  "nth(ms_,n_) = if n_ == 1 then head(ms_) else nth(tail(ms_), n_ - 1)\n\n"++
>  -- functions relating to timestamps
>  maybeString (hasFlag an TimestampsUsed) (timeStampFns an) ++
>  "-- add Garbage to a set that contains and encryption,\n"++
>  "-- hash function application of Vernam encryption\n\n"++
>  "addGarbage_(S_) =\n"++
>  "  if S_=={} then {Garbage}\n"++
>  "  else Union({S_, {Garbage | Encrypt._ <- S_}, \n"++
>  "             {Garbage | Hash._ <- S_},\n"++
>  "             {Garbage | Xor._ <- S_}})\n\n"

>  -- "nth(ms_,n_) = if n_ == 1 then rmts(head(ms_)) 
>  -- else nth(tail(ms_), n_ - 1)\n\n"++
>  -- "nthts(ms_,n_) = if n_ == 1 then head(ms_) 
>  -- else nthts(tail(ms_), n_ - 1)\n\n"++

The Encryption datatype

>encryption :: Annotated -> Output
>encryption an = 
>  let
>       sess_ids = if (sessinfo an /= []) then ", SessionIds" else ""
>       newchans = newchannels an
>       dtcons =  -- constructors of datatypes
>         [cons | (_,pats,_) <- dtdefs an, (cons,args) <- pats]
>  in
>  "-- Main datatype, representing all possible messages\n\n"++ 
>  "datatype Encryption =\n  " ++
>  -- "-- "++show (dtdefs an) ++ "\n-- " ++ show (fnts an) ++ "\n" ++
>  format 2 " | "
>     -- Actual values:
>    (remdups (actvtsnames an)++ ["Garbage"] ++ 
>     -- 0 arity datatype constructors:
>     [funname cons | (_,pats,_) <- dtdefs an, (cons,[]) <- pats] ++
>     [funname cons++".("++commaConcat(replicate (length args) "Encryption")
>        ++")" | 
>        (_,pats,_) <- dtdefs an, (cons,args) <- pats, args/=[]] ++
>     -- functions and non-0 arity datatype constructors
>     [funname f++"."++argType (fnts an) f |
>        (f, Symb _ _) <- fnts an, f `notElem` dtcons] ++
>     -- hash functions and timestamps 
>     [f | (f, HashFunction) <- fnts an] ++
>     (if hasFlag an TimestampsUsed then ["Timestamp.TS"] else []) ++
>     -- crypto-style constructors
>     ["Sq.Seq(Encryption)", "Encrypt.(ALL_KEYS,Seq(Encryption))", 
>      "Hash.(HashFunction, Seq(Encryption))", "Xor.(Encryption, Encryption)"] ++
>      -- (if unboundpar then ["Sent.(Encryption, Seq(Encryption))","Np_","Ns_","Ks_","Kp_"] else []))
>      -- Values to model channels
>      (if hasFlag an UnboundedParallel 
>       then ["Sent.(Encryption, Seq(Encryption))"] else []) ++
>      (if inUse ["C","NR-"] newchans 
>       then ["SentTo.(ALL_PRINCIPALS" ++ sess_ids ++ ", Encryption)"] 
>       else []) ++
>      (if inUse ["NF","NRA-"] newchans 
>       then ["SentBy.(ALL_PRINCIPALS" ++ sess_ids ++ ", Encryption)"] 
>       else []) ++
>      (if newchans == [] then [] 
>       else [
>         "SentByTo.(ALL_PRINCIPALS, ALL_PRINCIPALS"++sess_ids++
>           ", Encryption)",
>         "SentByToC.(ALL_PRINCIPALS, ALL_PRINCIPALS"++sess_ids++
>           ", Encryption)"]
>      ) ++
>      (if hasFlag an UnboundedParallel then 
>       ["AuthTaggedSignals"++show n++".AUTH"++show n++"_M__TaggedSignals"++
>           show n
>               | (n,_,_) <- authinfo an]
>       else [])
>    )
>  ++ "\n\n"


>argType fnts f =
>  let ats = findFnDomType fnts f
>      arity = length ats
>  in 
>  if arity==1 then hd ats 
>  else "("++commaConcat ats++")"

Functions related to timestamps

>timeStampFns :: Annotated -> Output
>timeStampFns an = 
>  -- "rmts(Timestamp.t_) = t_\n"++
>  -- "rmts(x_) = x_\n\n"++
>  "map(f_, <>) = <>\n"++
>  "map(f_, <x_>^xs_) = <f_(x_)>^map(f_,xs_)\n\n"++
>  "-- Decrement all timestamps by 1\n"++
>  "dects(t_) = if t_ > MinTime then t_-1 else t_\n"++
>  "updt(Timestamp.t_) = Timestamp.dects(t_)\n"++
>  "updt(Sq.es_) = Sq.map(updt,es_)\n"++
>  "updt(Encrypt.(k_,es_)) = Encrypt.(k_, map(updt,es_))\n"++
>  "updt(Hash.(f_,es_)) = Hash.(f_,map(updt,es_))\n"++
>  "updt(Xor.(e1_,e2_)) = Xor.(updt(e1_),updt(e2_))\n"++
>  ifAllFlagsString an [UnboundedParallel, TimestampsUsed] (
>    concat 
>      [let agreementFields = diffOneInstance ls [agent1, agent2]
>           agreementFieldsStr = 
>             agent1++(maybeString (not(isAliveness authtype)) ("."++agent2))++
>               (flatmap (\m -> "."++m) agreementFields)++".tag_"
>           fOriginal = "AUTH"++show n++"_M::TRunning"++show n++".ms_."++
>                       agreementFieldsStr
>           fNew = "AUTH"++show n++"_M::TRunning"++show n++".map(dects,ms_)."++
>                  agreementFieldsStr
>        in "updt("++fOriginal++") = "++fNew++"\n"
>       | (n,(a,b,authtype),((n1,agent1),(n2,agent2),ls)) <- 
>           authinfo an,isTimedAuth authtype]
>    )++
>    "updt(x_) = x_\n\n"

>produceTimeInfo NotUsed = ""
>produceTimeInfo (MRTUsed rt) = 
>  "-- Information about timestamps\n\n"++
>  "MaxRunTime = "++show rt++"\n\n"
>produceTimeInfo (TimeStampsUsed t0 t1 rt) =
>  "-- Information about timestamps\n\n"++
>  "now = 0\n"++
>  "MinTime = -" ++ show t1 ++ "\n" ++
>  "MaxTime = -" ++ show t0 ++ "\n" ++
>  "TS = {MinTime .. MaxTime}\n" ++
>  "MaxRunTime = " ++ show rt ++ "\n" ++
>  "TimeStamp = {Timestamp.t_ | t_ <- TS}\n" ++
>  "max(t0_,t1_) = if t0_>t1_ then t0_ else t1_\n" ++
>  "min(t0_,t1_) = if t0_>t1_ then t1_ else t0_\n\n"

=======================================================================
Produce channel definitions

>channeldefs :: Annotated -> [SessionId] -> Output
>channeldefs an sessids =
>  let	envmsgnos = 
>        [n | (_,n,Environment,_,_,_,_,_) <- protdes] ++
>        [n | (_,n,_,Environment,_,_,_,_) <- protdes]
>       Annotated {
>           protdesc = protdes, newchannels = newchans, 
>           channels = (_,authC,directC)} = an
>  in
>  "-- Message labels\n\n"++
>  "datatype Labels =\n  " ++
>  format 2 " | "
>    (["Msg" ++ n  | (_,n,Agent _,Agent _,_,_,_,_) <- protdes] ++
>     ["Env" ++ n  | n <- (if envmsgnos==[] then ["0"] else envmsgnos)]) ++
>  (if sessinfo an /= [] then
>   "\n\n"++
>    "datatype SessionIds =\n\t" ++
>    (format 2 " | " (
>      [cn | (_, _, cn) <- sessids]++
>      ["c_" ++ [head (intruderId an)]]
>    ))++"\n\n"++
>    concat
>      ["SessionId(Msg" ++ n ++ ") = {" ++
>        (format 2 ", "
>          ([cn | (_, (_, _, _, m, ms), cn) <- sessids, m==n || n `elem` ms]++
>           ["c_" ++ [head (intruderId an)]]
>          )
>        ) ++
>      "}\n" | (_,n,Agent _,_,_,_,_,_) <- protdes]
>  else "")
>  ++ "\n\n"++
>  -- "MSG = union(INPUT_MSG,OUTPUT_MSG)\n\n" ++
>  (if newchans == [] then 
>  "MSG_BODY = {ALGEBRA_M::applyRenaming(m_) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO}\n\n"
>  else 
>    (if sessinfo an /= [] then
>      "MSG_BODY_0 = {ALGEBRA_M::applyRenaming(m_) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO}\n" ++
>      "MSG_BODY_1 = " ++
>      makeUnion 2 [
>        "{SentTo.(B_, c_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", B_ <- ALL_PRINCIPALS, c_ <- SessionIds}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (channelIs ["C","NR-"] (channelSelect n newchans))
>      ] ++
>      "MSG_BODY_2 = " ++
>      makeUnion 2 [
>        "{SentBy.(A_, c_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", A_ <- ALL_PRINCIPALS, c_ <- SessionIds}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (channelIs ["NF","NRA-"] (channelSelect n newchans))
>      ] ++
>      "MSG_BODY_3 = " ++
>      makeUnion 2 [
>        "{SentByTo.(A_, B_, c_, ALGEBRA_M::applyRenaming(m_)), \n" ++
>          " SentByToC.(A_, B_, c_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS, c_ <- SessionIds}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (not (
>          channelIs ["NF","NRA-"] (channelSelect n newchans) || 
>          channelIs ["C","NR-"] (channelSelect n newchans) || 
>          channelIs [] (channelSelect n newchans))
>        )
>      ]
>    else
>      "MSG_BODY_0 = {ALGEBRA_M::applyRenaming(m_) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO}\n" ++
>      "MSG_BODY_1 = " ++
>      makeUnion 2 [
>        "{SentTo.(B_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", B_ <- ALL_PRINCIPALS}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (channelIs ["C","NR-"] (channelSelect n newchans))
>      ] ++
>      "MSG_BODY_2 = " ++
>      makeUnion 2 [
>        "{SentBy.(A_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", A_ <- ALL_PRINCIPALS}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (channelIs ["NF","NRA-"] (channelSelect n newchans))
>      ] ++
>      "MSG_BODY_3 = " ++
>      makeUnion 2 [
>        "{SentByTo.(A_, B_, ALGEBRA_M::applyRenaming(m_)), \n" ++
>          " SentByToC.(A_, B_, ALGEBRA_M::applyRenaming(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO" ++ n ++ 
>          ", A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS}" 
>        | (_,n,Agent _,Agent _,m,_,_,_) <- protdes, (not (
>          channelIs ["NF","NRA-"] (channelSelect n newchans) || 
>          channelIs ["C","NR-"] (channelSelect n newchans) || 
>          channelIs [] (channelSelect n newchans))
>        )
>      ]
>    )++
>  "MSG_BODY = Union({MSG_BODY_0, MSG_BODY_1, MSG_BODY_2, MSG_BODY_3})\n\n") ++
>  "-- Type of principals\n\n"++
>  "ALL_PRINCIPALS = " ++
>  (makeUnion 2 . remdups)
>      ([findtype an s | (_,_,Agent s,_,_,_,_,_) <- protdes] ++
>       [findtype an r | (_,_,_,Agent r,_,_,_,_) <- protdes]) ++
>  "\n" ++
>  "INTRUDER = "++intruderId an++"\n\n"++
>  "HONEST = diff(ALL_PRINCIPALS, {INTRUDER})\n\n"++
>  -- "REAL_HONEST = diff(HONEST, {"++commaConcat (intruderProcs an)++"}\n\n"++
>  "-- Channel declarations\n\n"++
>  "INPUT_MSG = SYSTEM_M::INPUT_MSG\n"++
>  "OUTPUT_MSG = SYSTEM_M::OUTPUT_MSG\n"++
>  "DIRECT_MSG = SYSTEM_M::DIRECT_MSG\n"++
>  "ENV_MSG :: {(Labels, Encryption, <Encryption>)}\n"++
>  "ENV_MSG = SYSTEM_M::ENV_MSG\n\n"++
>  (if sessinfo an /= [] then
>    "channel receive: ALL_PRINCIPALS.ALL_PRINCIPALS.SessionIds.INPUT_MSG\n"
>   else
>    "channel receive: ALL_PRINCIPALS.ALL_PRINCIPALS.INPUT_MSG\n"
>  )++
>  (if directC /= Some[] && authC /= All then
>      "channel comm: ALL_PRINCIPALS.ALL_PRINCIPALS.DIRECT_MSG\n"
>   else "")++
>  (if sessinfo an /= [] then
>    "channel send: ALL_PRINCIPALS.ALL_PRINCIPALS.SessionIds.OUTPUT_MSG\n"
>   else
>    "channel send: ALL_PRINCIPALS.ALL_PRINCIPALS.OUTPUT_MSG\n"
>  )++
>  "channel env : ALL_PRINCIPALS.ENV_MSG\n" ++
>  "channel error\n"++
>  "channel start, close : HONEST.HONEST_ROLE\n\n" ++
>  "channel leak : addGarbage_(ALL_SECRETS)\n" 

===========================================================================

============================================================================
Declare type of signals

>declareSignals an =
>  "-- Define type of signals, and declare signal channel\n\n"++
>  "datatype Signal = \n" ++
>  "  Claim_Secret.ALL_PRINCIPALS.ALL_SECRETS.Set(ALL_PRINCIPALS)" ++
>  concat
>    [let dsstring = flatmap (('.' :) . findtype an) ds
>     in 
>     " |\n  Running"++show n++".HONEST_ROLE.ALL_PRINCIPALS"++
>           (if hasFlag an UnboundedParallel 
>               && isAliveness at then "" else ".ALL_PRINCIPALS")++
>       dsstring++" |\n" ++
>     "  Commit"++show n++".HONEST_ROLE.ALL_PRINCIPALS.ALL_PRINCIPALS"++
>       dsstring++" |\n" ++
>     "  RunCom"++show n++".ALL_PRINCIPALS.ALL_PRINCIPALS"++dsstring++dsstring
>          | (n,(at,_,_,ds)) <- zip [1..] [(at, a,b,authArgs at) | (a,b,at)<-auths an]] 
>  ++ "\n\n" ++
>  "channel signal : Signal\n\n"

============================================================================

>timingDefs =
>  "-- Timing functions\n\n" ++
>  "channel tock\n\n" ++
>  -- allow up to n tocks before termination
>  "TOCKS(n_) = n_>0 & tock -> TOCKS(n_ - 1) [] SKIP\n" ++
>  -- allow arbitrary number of tocks before termination
>  "TSKIP = tock -> TSKIP [] SKIP\n" ++
>  -- allow arbitrary number of tocks before acting like P
>  "allowInitTocks(P_) = tock -> allowInitTocks(P_) [] P_\n" ++
>  -- time out process
>  "TIMEOUT = tock -> TSKIP\n" ++
>  -- allow up to n tocks during execution of P, 
>  -- arbitrary many before and after
>  "transparent explicate\n"++
>  "addTime(P_,n_) = explicate(allowInitTocks((P_ ||| TOCKS(n_)) /\\ TIMEOUT))\n\n"
>  -- in above, TIMEOUT cannot be replaced with its definition because of a
>  -- bug in the current release of FDR

