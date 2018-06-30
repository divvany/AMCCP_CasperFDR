Produce definition of system

>module System(produceActualAgents, produceActualSystem, produceActualSystem0, pickSessionIds) where

>import Useful
>import Pprint
>import Annotated
>import Types
>import SecureChannels

============================================================================

Print arguments in parentheses, separated by commas

>showArgs :: [String] -> String
>showArgs args = "(" ++ commaConcat args ++ ")"

============================================================================

>produceActualAgents :: Annotated -> Output
>produceActualAgents an = 
>  let procnames = remdups [pn | (_,pn,_,_,_) <- procs an]
>      groupedAgents = -- group together agents with same name and role
>        groupAgents an procnames ids (actualAgents an)
>      ids0 = [a | (a,_,_,_,_) <- procs an]
>      idsTypes = remdups (map (findtype an) ids0)
>          -- Names of actual agents in system
>      ids = remdups (remove (flatmap (allOfType an) idsTypes) (intruderId an))
>      sessids = sessionids (sessinfo an) (procs an) (protdesc an) (actualAgents an)
>  in flatmap (makeAgent an sessids) groupedAgents ++
>  (if filter ((== 1) . (\ (a,b,c) -> b)) (sessinfo an)  /= [] then
>  "-- Connection manager\n\n" ++ 
>  "  InjectiveSessionIds = {" ++ commaConcat [cn | (_,(_,_,_,m,ms),cn) <- sessids, (_,1,ns) <- sessinfo an, m `elem` ns] ++ "}\n\n" ++ 
>  "  CONNECTION_MANAGER(c_) =\n    [] B_ : ALL_PRINCIPALS @ allocate.B_.c_ -> STOP\n\n" ++
>  "  CONN_MANAGER_0 = ||| c_ : InjectiveSessionIds @ CONNECTION_MANAGER(c_)\n\n" ++
>  "  Alpha_ConnManager = {| receive.A_.B_.c_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS, c_ <- InjectiveSessionIds |}\n\n"
>  else "")

======================================================================

*** Treat SeqComps properly

Group together all agents with the same name and role.  Returns a list of
triples of the form (id,pnaass) where id is an agent identity, and pnass is a
list of triples of the form (pn,fid,argsss), where pn is a process name
represent the role represented by the process name pn, fid is the identity
that represents pn in the protocol description, and argsss is a list of
elements argss, where each argss represents a sequential composition of
processes with parameters args (for args <- argss).

>groupAgents :: 
>  Annotated -> [ProcessName] -> [Argument] -> [SeqActualAgent] -> 
>    [(Argument, [(ProcessName, Argument, [[[Argument]]])])]
>groupAgents _ _ [] [] = []
>groupAgents an procnames (id:ids) agents =
>  -- group together all processes with identity id
>  (id, groupAgents1 an procnames matches) : 
>  -- now group together the rest
>  groupAgents an procnames ids rest
>  where matches = [SeqComp aas | SeqComp aas <- agents, (hd.snd.hd) aas == id]
>        rest = [SeqComp aas | SeqComp aas <- agents, (hd.snd.hd) aas /= id]
>groupAgents _ _ xs ys = error (show xs++"\n"++show ys)

Group together according to process name

>groupAgents1 :: 
>  Annotated -> [ProcessName] -> [SeqActualAgent] -> 
>  [(ProcessName, Argument, [[[Argument]]])]
>groupAgents1 _ [] [] = []
>groupAgents1 an (pn:pns)  agents =
>  -- group together all agents with identity pn
>  (pn, protdescid (procs an) pn, matches) :
>  -- then group together the rest
>  groupAgents1 an pns rest
>  where matches = [map (tl.snd) aas | SeqComp aas <- agents, 
>                                      (fst.hd) aas == pn]
>        rest = [SeqComp aas | SeqComp aas <- agents, (fst.hd) aas /= pn]

Identity representing a particular role in protocol description

>protdescid :: ProcessList -> ProcessName -> Argument
>protdescid procs pn = hd [a | (a,pn',_,_,_) <- procs, pn == pn']

======================================================================
Define process representing one particular agent

>makeAgent :: Annotated -> [SessionId] -> (Argument, [(ProcessName, Argument, [[[Argument]]])]) -> 
>  Output

>makeAgent an sessids (id, pnass) = 
>  "  -- Process representing "++id++"\n\n" ++
>  ---- Processes for each role
>  let  id_roles = [fid | (_,fid,_:_) <- pnass]
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>       sessids' = [(i, (pn,pid,aid,n,ms), sid) | (i, (pn,pid,aid,n,ms), sid) <- sessids, aid==id]
>       Annotated {
>           channels = (_, authC, directC)
>       } = an
>  in
>  flatmap (makeAgent1 an sessids' id) pnass ++
>  ---- Total process alphabet
>  "  "++alphabetName id ++ " = " ++
>  makeUnion 4 (
>    ("{|env."++id++"|}") :
>    ("{|send."++id++".A_"++sessString++" | A_ <- ALL_PRINCIPALS"++sessString'++"|}") :
>    (["{|receive."++id++".A_"++
>      ".m_ | A_ <- ALL_PRINCIPALS, m_ <- INPUT_MSG"++n++"|}" |
>           (_,n,Agent a,Agent _,_,_,_,_) <- protdesc an, isIn n authC ]) ++
>    --       (_,n,Agent a,Agent _,_,_,_,_) <- protdesc an, a `elem` id_roles, isIn n authC ]) ++
>    -- The easiest solution to this problem is to make the agent synchronize on all receive events
>    -- another agent might accept, whether they could send them or not.  It makes the alphabet slightly
>    -- larger than it needs to be, so it might be better to calculate the id_roles differently.
>    (["{|receive.A_."++id++sessString++
>      ".m_ | A_ <- ALL_PRINCIPALS, m_ <- INPUT_MSG"++n++sessString'++"|}" |
>           (_,n,Agent _,Agent b,_,_,_,_) <- protdesc an, b `elem` id_roles ]) ++
>    ([if a `elem` id_roles && b `elem` id_roles then 
>        "{|comm."++id++".A_.m_, comm.A_."++id++".m_ |\n"++
>        "       A_ <- ALL_PRINCIPALS, m_ <- INT_MSG_INFO"++n++"|}"
>      else 
>        "{|comm."++id++".A_.m_, comm.A_."++id++".m_ |\n"++
>        "       A_ <- ALL_PRINCIPALS, A_ != "++id++
>        ", m_ <- INT_MSG_INFO"++n++"|}" |
>           (_,n,Agent a,Agent b,_,_,_,_) <- protdesc an,
>                                            isIn n directC && not (isIn n authC) ]
>        -- ++
>        -- ["{|comm."++id++".A_, comm.A_."++id++" | A_ <- ALL_PRINCIPALS|}"]
>    ) ++
>    (if filter ((== 2) . (\ (a,b,c) -> b))  (sessinfo an) /= [] then
>       ["{|pair.c_A, pair.c_.c_A | c_ <- SessionIds, c_A <- {"++
>      (commaConcat [c | c <- map trd sessids']) ++ "} |}"] else []) ++
>    (if hasFlag an TimeUsed then ["{tock}"] else [] ) ++
>    ( if hasFlag an CrackablesUsed then ["{|close."++id++"|}"] else [] )
>  )++"\n"
>  ++
>  ---- Block comms from this agent to itself if using auth channels
>  (if (authC /= Some []) then "  "++id++"BlockSet =\n"++
>  "    let self_comms = {|receive."++id++"."++id++".m_ | m_ <- "++
>  makeUnion 0 ["INPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdesc an, isIn n authC]++ "|}\n"++
>  concat
>    ["        "++alphabetName1 pn id++"_receive = \n"++
>     "          inter(self_comms, "++alphabetName1 pn id++")\n" |
>       pn <- pns] ++
>  "      allowSet = "++
>  makeUnion 10
>    ["inter("++alphabetName1 pn1 id++"_receive, "++
>     alphabetName1 pn1 id++"_receive)" | 
>       pn1 <- pns, pn2 <- pns, pn1<pn2] ++
>  "    within diff(self_comms, allowSet)"++
>  "\n\n" else "")
> ++ 
>  ---- Total process for this agent
>  "  "++processName id ++ " =" ++ 
>  ( if pns==[] then if hasFlag an TimeUsed then " RUN({|tock|})" else " STOP" 
>    else 
>      "\n    " ++ 
>      makeParallel --  *** --(if authC then block BlockSet
>         [(processName1 id pn, alphabetName1 pn id) | pn <- pns] ++
>      maybeString (authC /= Some []) ("\n      [| "++id++"BlockSet |] STOP") 
>  )++ 
>  "\n\n"
>  where -- fids = [fid | (_,fid,_:_) <- pnass]
>          -- free vars in protdesc representing id
>        pns = [pn | (pn,_,_:_) <- pnass]


>processName id = "AGENT_" ++ id
>alphabetName id = "Alpha_" ++ id

>pickSessionIds [] _ = []
>pickSessionIds _ [] = []
>pickSessionIds ms sids = (map trd used) : pickSessionIds ms unused
>  where (used,unused) = pickSessionIds' ms sids ([],[])

>pickSessionIds' ms [] (used,unused) = (used,unused)
>pickSessionIds' ms (sid:sids) (used,unused) = 
>  let (_,(_,_,_,n,_),_) = sid in
>  if n `elem` ms then pickSessionIds' (filter (/= n) ms) sids (used++[sid],unused)
>  else pickSessionIds' ms sids (used,unused++[sid])

>trd (_,_,a) = a

>combineSessionIds x [] = x
>combineSessionIds [] _ = []
>combineSessionIds (a:as) sids = a':combineSessionIds as sids'
>  where (a', sids') = distributeSessionIds a ([], sids)

>distributeSessionIds [] (as', sids') = (as', sids')
>distributeSessionIds (a:as) (as', (sid':sids')) = distributeSessionIds as (as'++[a++sid'], sids')

Define process representing one particular agent in one particular role

>makeAgent1 :: Annotated -> [SessionId] -> String -> (ProcessName, Argument, [[[Argument]]]) -> 
>  Output
>makeAgent1 an sessids id (pn, fid, argsss) = 
>   let
>       Annotated {
>           channels = (_, authC, directC)
>       } = an
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>       sessids_init = [n | (_,_,ms) <- sessinfo an, m <- ms, (_,n,Agent a,Agent b,_,_,_,_) <- protdesc an, a==fid, n==m]
>       sessids_args = pickSessionIds sessids_init sessids
>       argsss' = combineSessionIds argsss sessids_args
>  in
>  if argsss == [] then "" else
>  ---- alphabet
>  "  "++alphabetName1 pn id ++ " = " ++
>  makeUnion 4 ( 
>    ["{|env."++id++".m_ | m_ <- ENV_MSG"++n++"|}" |
>         (_,n,Environment,Agent b,_,_,_,_) <- protdesc an, b==fid] ++ 
>    ["{|env."++id++".m_ | m_ <- ENV_MSG"++n++"|}" |  
>         (_,n,Agent a,Environment,_,_,_,_) <- protdesc an, a==fid] ++ 
>    ["{|send."++id++".A_"++sessString++".m_ | A_ <- ALL_PRINCIPALS, m_ <- OUTPUT_MSG"
>	++n++sessString'++"|}" |  
>         (_,n,Agent a,Agent _,_,_,_,_) <- protdesc an, a == fid]++ 
>    ["{|receive."++id++".A_.m_ | A_ <- ALL_PRINCIPALS, m_ <- INPUT_MSG"   
>	++n++"|}" | 
>             (_,n,Agent a,Agent _,_,_,_,_) <- protdesc an, a == fid, isIn n authC] 
>    ++ 
>    ["{|receive.A_."++id++sessString++".m_ | A_ <- ALL_PRINCIPALS, m_ <- INPUT_MSG"
>	  ++n++sessString'++"|}" | 
>           (_,n,Agent _,Agent b,_,_,_,_) <- protdesc an, b == fid] ++
>    ["{|comm.A_."++id++".m_ | "++
>         "A_ <- ALL_PRINCIPALS, m_ <- INT_MSG_INFO"++n++"|}" |
>           (_,n,Agent _,Agent b,_,_,_,_) <- protdesc an, b == fid,
>           isIn n directC && not (isIn n authC)] ++
>    ["{|comm."++id++".A_.m_ | "++
>         "A_ <- ALL_PRINCIPALS, m_ <- INT_MSG_INFO"++n++"|}" |
>           (_,n,Agent a,Agent _,_,_,_,_) <- protdesc an, a == fid,
>           isIn n directC && not (isIn n authC)] ++
>    (if filter ((== 2) . (\ (a,b,c) -> b)) (sessinfo an) /= [] then
>       ["{|pair.c_A, pair.c_.c_A | c_ <- SessionIds, c_A <- {"++
>      (commaConcat [c | c <- concat sessids_args]) ++ "} |}"] else [] )++
>    (if hasFlag an TimeUsed then ["{tock}"] else [])
>    ++
>    (if hasFlag an CrackablesUsed then ["{|close."++id++"."++pn++"_role|}"] else [])
>  ) ++
>  "\n" ++
>  ---- process definition
>  "  "++processName1 id pn ++ " = " ++
>  interleave (hasFlag an TimeUsed) 
>    [seqcomp (hasFlag an TimeUsed) [pn ++ showArgs ((if hasFlag an TimeUsed then ["MaxRunTime"] else [])++id:args) | args <- argss] | 
>       argss <- argsss'] ++ 
>  "\n\n"

>processName1 id pn = pn ++ "_" ++ id
>alphabetName1 procName id = "Alpha_" ++ procName ++ "_" ++ id

>seqcomp timeUsed [] = if timeUsed then "RUN({tock})" else "SKIP"
>seqcomp timeUsed sts =  "("++foldr sc b sts ++ ")"
>  where 
>       sc p p' = p ++ " ; " ++ p'
>       b = if timeUsed then "RUN({tock})" else "STOP"

----

Make parallel composition of a list of (ProcessName, Alphabet) pairs.

>makeParallel :: [(String, String)] -> String
>makeParallel [] = "STOP"
>makeParallel  [(p,a)] = "("++p++" ["++a++" || {} ] STOP)"
>  -- I'm not sure if that's necessary!
>makeParallel pas = fst (foldr1 makepar pas)
>  where makepar (p1,a1) (p2,a2) = 
>          ("(" ++ p1 ++ "\n      ["++a1++"||"++a2++"]\n    " ++ 
>              p2 ++ ")",  
>           "union(" ++ a1 ++ ", " ++ a2 ++ ")") 

          ("(" ++ p1 ++ "\n    [| inter("++a1++", "++a2++") |]\n  " ++
              p2 ++ ")", 
           "union(" ++ a1 ++ ", " ++ a2 ++ ")")

>interleave _ [] = "STOP" 
>interleave timeUsed sts = foldr1 int sts 
>  where int p p' = 
>          if timeUsed
>          then "(" ++ p ++ "\n    [|{tock}|]\n    " ++ p' ++ ")" 
>          else "(" ++ p ++ "\n    |||\n    " ++ p' ++ ")" 

======================================================================
Produce definition of actual system, excluding intruder

>produceActualSystem0 :: Annotated -> Output
>produceActualSystem0 an = 
>  let 
>      Annotated {
>          channels = (_,authC,_)
>      } = an
>      ids0 = [a | (a,_,_,_,_) <- procs an]
>      idsTypes = remdups (map (findtype an) ids0)
>          -- Names of actual agents in system
>      ids = remove (flatmap (allOfType an) idsTypes) (intruderId an)
>  in
>     "  -- Complete system\n\n" ++ 
>-- if injective or symmetric session channels are used we need the session manager
>     (if filter ((>= 1) . (\ (a,b,c) -> b)) (sessinfo an) == [] then
>     "  SYSTEM_0 =\n    " 
>     else
>     "  SYSTEM_00 =\n    " 
>     ) ++    
>     makeParallel (remdups [(processName id, alphabetName id) | id <- ids])++"\n\n"++
>-- if injective session channels are used we need the session manager
>     (if filter ((== 1) . (\ (a,b,c) -> b)) (sessinfo an) /= [] then
>     "  CONN_MANAGER = CONN_MANAGER_0\n    " ++
>     "[[ allocate.B_.c_ <- receive.A_.B_.c_.ALGEBRA_M::rmb((l_, m_, re_)) |\n       " ++
>     "A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS,\n       " ++
>     "c_ <- InjectiveSessionIds, (l_, m_, se_, re_) <- INT_MSG_INFO ]]\n\n" ++
>     "  SYSTEM_0 = \n    SYSTEM_00\n      [ Union({" ++ 
>     commaConcat [alphabetName id | id <- ids] ++ 
>     "}) || Alpha_ConnManager ]\n    CONN_MANAGER" ++ "\n\n"
>     else "") ++
>-- if symmetric session channels are used we need the session pair manager
>-- to make sure agents can always pair with the intruder's session id
>     (if filter ((== 2) . (\ (a,b,c) -> b)) (sessinfo an) /= [] then
>     "  SYSTEM_0 = SYSTEM_00 \\ {|pair|}\n\n"
>     -- The following makes no sense to me (and "c_M" assumes the intruder's
>     -- name starts with "M")
>     -- "  PAIR_MANAGER =    [] c_A:SessionIds @ pair.c_A.c_M -> PAIR_MANAGER\n" ++
>     -- "                 [] [] c_A:SessionIds @ pair.c_M.c_A -> PAIR_MANAGER\n\n" ++
>     -- "  SYSTEM_0 = (SYSTEM_00 [| {|pair.c_A.c_" ++ [head (intruderId an)] ++ 
>     -- ", pair.c_" ++ [head (intruderId an)] ++ ".c_A | c_A : SessionIds|} |] " ++
>     -- "PAIR_MANAGER) \\ {|pair|}\n\n"
>     else "")

======================================================================
Produce definition of actual system, including intruder

>produceActualSystem :: Annotated -> Output
>produceActualSystem an = 
>  let 
>       Annotated {
>           channels = (secC,authC,directC),
>           protdesc = protdes,
>           intruderId = intruder
>       } = an
>       sys0name = "SYSTEM_M::SYSTEM_0"
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>  in
>     "IntruderInterface = " ++
>     makeUnion 2 (
>     -- messages sent by intruder
>       -- authenticated messages
>       ["{| receive."++intruder++".A_.m_ | A_ <- ALL_PRINCIPALS, m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::INPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes, isIn n authC])++
>        " |}"]++
>       -- unauthenticated messages
>       ["{| receive.A_.B_" ++ sessString ++ ".m_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS" ++ sessString' ++ ", m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::INPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes, not (isIn n authC)])++
>        " |}"]++
>    -- messages heard by intruder
>      -- secret and authenticated messages
>       ["{| send.A_."++intruder++".m_ | A_ <- ALL_PRINCIPALS, m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::OUTPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      isIn n authC && isIn n secC ])++
>        " |}"]++
>      -- just authenticated messages
>       ["{| send.A_.B_.m_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS, m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::OUTPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      isIn n authC && not (isIn n secC) ])++
>        " |}"]++
>      -- just secret messages
>       (if (directC /= Some[] && authC /= All) then
>        ["{| comm.A_."++intruder++".m_, comm."++intruder++".A_.m_ | A_ <- ALL_PRINCIPALS, m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      isIn n secC && not (isIn n authC) ])++
>        " |}"] else [])++
>      -- just direct messages
>       ["{| send.A_.B_.m_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS, m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::OUTPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      isIn n directC && not (isIn n authC || isIn n secC) ])++
>        " |}"]++ 
>       (if (directC /= Some[] && authC /= All) then
>        ["{| comm.A_.B_.m_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS,m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      isIn n directC && not (isIn n authC || isIn n secC) ])++
>        " |}"] else [])
>      ++
>      -- everything else
>       ["{| send.A_.B_" ++ sessString ++ ".m_ | A_ <- ALL_PRINCIPALS, B_ <- ALL_PRINCIPALS" ++ sessString' ++ ", m_ <- "++
>            makeUnion' 4 (["SYSTEM_M::OUTPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                                      not (isIn n directC) ])++
>        " |}"]++
>       (if hasFlag an TimestampsUsed then ["{tock}"] else [])++
>       (if hasFlag an CrackablesUsed then ["{|crack|}"] else [])
>     ) ++
>     "\n" ++
>     (if hasFlag an CrackablesUsed then 
>        let moduleName = "CRACKING_M"
>        in
>	 "AlphaSystem = {|env, send, receive, close"++
>        (if hasFlag an TimestampsUsed || hasFlag an TimedCracking then ", tock" else "")++
>        "|}\n\n" ++
>	 "SystemManagerInterface = inter(AlphaSystem,"++
>           moduleName++"::AlphaManager)\n\n"++
>	 "SYSTEM = ("++sys0name++" [|SystemManagerInterface|] "++
>        moduleName++"::Manager)\n"++ 
>	 "            [|IntruderInterface|] INTRUDER_M::BUILD_INTRUDER(INTRUDER_M::INTRUDER_0)\n\n"
>      else 
>        ifNotFlagString an UnboundedParallel
>	       ("SYSTEM = \n  "++sys0name++" [| IntruderInterface |] INTRUDER_M::BUILD_INTRUDER(INTRUDER_M::INTRUDER_0)\n\n") )


Following seems no longer to be used anywhere

     ++
     maybeString (hasFlag an TimedAuth && not (hasFlag an TimestampsUsed || hasFlag an TimedCracking)) (
	 "TIMED_SYSTEM = \n"++
        "  SYSTEM_M::TIMED_SYSTEM_0 [| {|tock, send, receive|} |] INTRUDER_M::BUILD_INTRUDER(INTRUDER_M::INTRUDER_0)\n\n"
     )

