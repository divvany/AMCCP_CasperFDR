>module Cracking(printKCManagers) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import Annotated
>import Accumulation

-----------------------------------------------------------------------
printKCManager
-----------------------------------------------------------------------

>printKCManagers :: Annotated -> Output
>printKCManagers an =
>  if crackables an==[] then ""
>  else
>   let agentLink = linkProcAgents an
>       untimedCracking = or [ti==Nothing | (_,ti) <- crackables an]
>   in heading "Key compromise" ++ 
>      "module CRACKING_M\n\n"++
>      maybeString untimedCracking (makeRoles agentLink) ++
>      flatmap (makeKeyCompromiseManager an agentLink accumList) (crackables an) ++
>      "exports\n\n"++
>      "  ALL_CRACKABLES = "++makeUnion 2 (map fst (crackables an))++"\n"++
>      makeAllTypesKeyCompromiseManager an ++
>      "endmodule\n\n" ++
>      "ALL_CRACKABLES = CRACKING_M::ALL_CRACKABLES\n"++
>      "channel crack : ALL_CRACKABLES\n\n"
>   where accumList = accumulation' (protdesc an)

-----------------------------------------------------------------------
makeKeyCompromiseManager
-----------------------------------------------------------------------

Return a string representing the CSP code for the managers dealing with key
compromise for a particular type.

>makeKeyCompromiseManager an agentLink accumList (typeId, Nothing) =
>  let
>	thisAccumList = makeSpecificAccumList an typeId accumList
>	picks = [(nr,s,sl) | (nr,(s,sl),_) <- thisAccumList, sl/=[],
>				not(member s (intruderProcs an))]
>	tolds = [(nr,r,rl) | (nr,_,(r,rl)) <- thisAccumList, rl/=[]]
>	procId = remdups[(id,pr) | (id,pr,_,_,_) <- procs an, 
>                           (_,(s,_),(r,_)) <- thisAccumList, s==id || r==id]
>  in "  -- Untimed key manager for type "++typeId++"\n\n"++
>     indentHeading 2  ("Key compromise manager for "++typeId)++
>     "  module "++typeId++"CRACKING_M\n\n"++
>     makeParMonitorProcess typeId picks tolds False agentLink ++
>     defMsgSets2 an typeId procId thisAccumList False ++ 
>     makeRenMonitor typeId thisAccumList agentLink ++
>     makeCracker typeId ++
>     makeCracker_r an agentLink typeId ++
>     makeMan1 typeId ++
>     "  exports\n\n"++
>     makeChannelDefs1 typeId picks tolds agentLink False ++
>     makeMan typeId ++
>     "  endmodule\n\n"

Timed case:

>makeKeyCompromiseManager an agentLink accumList (typeId, Just t) =
>  let
>	thisAccumList = makeSpecificAccumList an typeId accumList
>	picks = [(nr,s,sl) | (nr,(s,sl),_) <- thisAccumList, sl/=[],
>				not(member s (intruderProcs an))]
>	tolds = [(nr,r,rl) | (nr,_,(r,rl)) <- thisAccumList, rl/=[]]
>	procId = remdups[(id,pr) | (id,pr,_,_,_) <- procs an, 
>                           (_,(s,_),(r,_)) <- thisAccumList, s==id || r==id]
>  in "  -- Timed key manager for type "++typeId++"\n\n"++
>     indentHeading 2  ("Key compromise manager for "++typeId)++
>     "  module "++typeId++"CRACKING_M\n\n"++
>     defMsgSets2 an typeId procId thisAccumList True ++ 
>     makeTimedCracker thisAccumList agentLink typeId t ++
>     makeTimedRenCracker typeId thisAccumList agentLink ++
>     "  exports\n\n"++
>     makeChannelDefs1 typeId picks tolds agentLink True ++
>     makeTimedMan typeId ++
>     "  endmodule\n\n"

-------------------------------------------------------------------------
defMsgSets2

called by makeKeyCompromiseManager
-------------------------------------------------------------------------
Create event sets that int_Pick and int_Told events will get renamed to.

>defMsgSets2 :: Annotated -> TypeName -> [(String,ProcessName)] -> FreshVarList -> Bool -> Output
>defMsgSets2 an typeId procId thisAccumList timedCracking =
>  let  allinfo_prot = [(nr,id,ls) | (nr,id,ls) <- extrainfo an,
>                       (_,n,s,r,_,_,_,_)<- protdesc an, nr==n,
>                       s/=Environment && r/=Environment]
>       inputExtra = [(nr,ls) | (nr,id,ls) <- allinfo_prot,
>               (_,nr',_,r,_,_,_,_) <- protdesc an,nr==nr',Agent id==r] 
>       outputExtra = [(nr,ls) | (nr,id,ls) <- allinfo_prot,
>               (_,nr',s,_,_,_,_,_) <- protdesc an,nr==nr',Agent id==s] 
>       makeFresh = [(nr,s,sl,extra nr outputExtra) | 
>			(nr,(s,sl),_) <- thisAccumList, sl /= [],
>			not(member s (intruderProcs an))]
>       getNew = [(nr,r,rl,extra nr inputExtra) | 
>			(nr,_,(r,rl)) <- thisAccumList, rl /= []]
>	extra _ [] = []
>	extra n ((nr,ls):xs) = if (n==nr) then ls else extra n xs
>  in
>   "    -- Create sets of network events that "++typeId++"Monitor's\n"++
>   "    -- int_Pick events will get renamed to.\n\n"++
>   concat -- for the make sets
>    [concat
>      [let sm = senderMsg m
>       in
>       "    make"++typeId++pr++n++"_"++v++"("++s++","++v++") = \n"++
>       "      {send."++s++"."++r++".ALGEBRA_M::rmb((Msg"++n++", "++
>       showMsg an sm++", <"++commaConcat ls++ ">)) |\n"++
>       spaces 9++
>       format 9 ", " (makeVarGens an
>        (remdups((varFields2 ls
>		   ++varFields sm++varFields2 [r])\\(varFields2([id,v])))))
>       ++ "}\n\n" | v <- sl]
>     ++
>     "    make"++typeId++pr++n++"("++s++", k_) = "++
>     makeUnion 6 ["make"++typeId++pr++n++"_"++v++"("++s++", k_)" | v <- sl]++
>     "\n" | 
>        (n,s,sl,ls) <- makeFresh, (id,pr) <- procId, id==s,
>        (_,nr,_,Agent r,m,_,_,_) <- protdesc an, n==nr
>    ]
>   ++
>   (if timedCracking then ""
>    else
>     "    -- Create sets of network events that "++typeId++"Monitor's\n"++
>     "    -- int_Told events will get renamed to.\n\n"++
>     concat -- for the get sets
>      [concat
>        ["    get"++typeId++pr++n++"_"++v++"("++r++","++v++") =\n"++
>         "      {receive."++s++"."++r++".ALGEBRA_M::rmb((Msg"++n++", "++
>         showMsg an (varMsg m)++", <"++
>         commaConcat(map (\v -> if v=="now" then "Timestamp.now" else v) ls)++
>         ">)) |\n"++
>         spaces 9++
>         format 9 ", " (makeVarGens an
>          (remdups((varFields2 ls++
>	  		varFields m++varFields2 [s])\\(varFields2(id:rl)))))
>         ++ "}\n\n" | v <- rl]
>       ++
>       "    get"++typeId++pr++n++"("++r++", k_) = "++
>       makeUnion 6 ["get"++typeId++pr++n++"_"++v++"("++r++", k_)" | v <- rl]++
>       "\n" |
>          (id,pr) <- procId, (n,r,rl,ls) <- getNew, id==r, 
>          (_,nr,Agent s,_,m,_,_,_) <- protdesc an, n==nr
>      ]
>   )

rename Pick and told events in Manager

>makeRenMonitor typeId thisAccumList agentLink = 
> let 
>   pickList = [(nr,s,sl) | (nr,(s,sl),_) <- thisAccumList, sl/=[]]
>   toldList = [(nr,r,rl) | (nr,_,(r,rl)) <- thisAccumList, rl/=[]]
> in
>   "    -- Rename int_Pick and int_Told events to network events.\n\n"++
>   spaces 4++typeId ++ "RenMonitor(k_) =\n" ++ 
>   spaces 6++typeId++"Monitor(k_,{}) \n" ++
>   concat 
>    [spaces 8++"[["++id++"_int_Pick"++nr++"_"++typeId++".k_ <- m_ |\n" ++
>     spaces 12++"m_ <- make"++typeId++proc++nr++"("++id++", k_)]]\n" |
>        (nr,s,_) <- pickList, (a,proc,ls) <- agentLink, s==a, id <- ls]
>   ++
>   concat 
>    [spaces 8++"[["++id++"_int_Told"++nr++"_"++typeId++".k_ <- m_ |\n" ++
>     spaces 12++"m_ <- get"++typeId++proc++nr++"("++id++", k_)]]\n" |
>        (nr,r,_) <- toldList, (a,proc,ls) <- agentLink, r==a, id <- ls]
>   ++"\n"++
>   spaces 4++"alpha"++typeId ++ "RenMonitor(k_) = " ++
>   makeUnion 6
>    (("{|close, manSync1_"++typeId ++".k_|}") :
>--    ("{|close, manSync1_SessionKey.k_|}" :
>     ["make"++typeId++proc++nr++"("++id++", k_)" |
>        (nr,s,_) <- pickList, (a,proc,ls) <- agentLink, s==a, id <- ls] ++
>     ["get"++typeId++proc++nr++"("++id++", k_)" |
>        (nr,r,_) <- toldList, (a,proc,ls) <- agentLink, r==a, id <- ls]) 
>  ++ "\n"

Produce Cracker process

>makeCracker typeId =
>  let procName s = typeId++"Cracker(k_, "++s++")"
>      procName' s = typeId++"Cracker'(k_, "++s++")"
>  in "    -- Cracker for type "++typeId++"\n\n"++
>     "    -- Keep track of who is running.  When signalled on\n"++
>     "    -- manSync1_"++typeId++", wait for all those agents to close\n"++
>     "    -- (process "++typeId++"Cracker'), then crack key.\n\n"++
>     spaces 4++procName "S_"++" =\n"++
>     "      start?a_?t_:roles(a_) -> "++procName "union(S_,{(a_,t_)})"++"\n"++
>     "      [] close?a_?t_:roles(a_) ->" ++procName "diff(S_,{(a_,t_)})"++"\n"++
>     "      [] manSync1_"++typeId++".k_ ->\n"++
>     "           if S_=={} then crack.k_ -> "++procName' "S_"++"\n"++
>     "           else "++procName' "S_"++
>     "\n\n"++
>     spaces 4++procName' "S_"++" =\n"++
>     "      start?a_?t_:roles(a_) -> " ++procName' "S_"++"\n"++
>     "      [] close?a_?t_:roles(a_) ->\n" ++
>     "           if S_=={(a_,t_)} then crack.k_ -> "++procName' "{}"++"\n"++
>     "           else "++procName' "diff(S_,{(a_,t_)})"++
>     "\n\n"


----------------------------------------------------------------------
Rename start events of Cracker

>makeCracker_r an agentLink typeId =
>  let showEvent (nr, c) = 
>        c++"."++
>        (if c=="send" then "a_.b_" 
>         else if c=="receive" then "b_.a_" else "a_")++
>        "."++showTuple (nr, c)
>      showTuple (nr, c) = 
>        "("++(if c=="env" then "Env" else "Msg") ++ nr ++", m_, extras_)"
>      showRanges (nr, c, s) = 
>        "a_ <- HONEST, "++showTuple (nr, c)++" <- SYSTEM_M::"++s++
>        if c=="env" then "" else ",\n"++spaces 12++"b_ <- ALL_PRINCIPALS"
>  in
>  "    -- Rename start events to network events.\n\n"++
>  spaces 4++typeId++"Cracker_r(n_) =\n"++
>  spaces 6++typeId++"Cracker(n_,{})\n"++
>  concat
>    [let (nr, c, s) = firstEventSetChannel an id
>     in spaces 8++"[[start.a_."++r++"_role <- "++showEvent (nr, c)++" |\n"++
>        spaces 12++showRanges (nr, c, s)++"]]\n" | 
>          (id,r,_) <- agentLink]++
>  "\n"++
>  spaces 4++"alpha"++typeId++"Cracker_r(n_) = "++
>  makeUnion 6 
>    (("{|close, crack.n_, manSync1_"++typeId++".n_|}") :
>   --  ("{|close, crack.n_, manSync1_SessionKey.n_|}" :
>     [let (nr, c, s) = firstEventSetChannel an id
>      in "{"++showEvent (nr, c)++" |\n"++spaces 12++showRanges (nr, c, s)++"}" | 
>           (id,_,_) <- agentLink]) ++
>  "\n"

---------------------------------------------------------
Produce timed Cracker process

>makeTimedCracker thisAccumList agentLink typeId crackTime =
>  let procName = typeId++"Cracker(k_)"
>      procName' cT = typeId++"Counter(k_,"++cT++")"
>      -- procName_r s = typeId++"Cracker'(k_, "++s++")"
>      picks = [(nr,s,sl) | (nr,(s,sl),_) <- thisAccumList, sl/=[]] 
>      -- tolds = [(nr,r,rl) | (nr,_,(r,rl)) <- thisAccumList, rl/=[]]
>      -- procsId = labelBack "_" [id | (_,id,ls) <- agentLink, ls /= []]
>      pickList = 
>        [id++"_int_Pick"++nr++"_"++typeId ++".k_ -> "++
>         procName' (show crackTime) |
>           (nr,s,_) <- picks, (a,_,ls) <- agentLink, s==a, id <- ls]
>  in "    -- Timed cracker for type "++typeId++"\n"++
>     "    -- When agent first gets value, wait for "++show crackTime++
>     " time units, then crack key.\n\n"++
>     spaces 4++procName++" =\n"++
>     distributeA 6 "[] " pickList ++ "\n"++
>     "      [] tock -> "++procName++"\n\n"
>     ++
>     spaces 4++procName' "ct_" ++" =\n"++
>     "      if ct_==0 then crack.k_ -> "++procName++" [] tock -> "++(procName' "ct_")++"\n"++
>     "      else tock -> "++procName' "ct_-1"++"\n\n"

----------------------------------------------------------
rename told events in Timed Cracker

>makeTimedRenCracker typeId thisAccumList agentLink = 
> let 
>   pickList = [(nr,s,sl) | (nr,(s,sl),_) <- thisAccumList, sl/=[]]
>   -- toldList = [(nr,r,rl) | (nr,_,(r,rl)) <- thisAccumList, rl/=[]]
> in
>   "    -- Rename int_Pick events to network events.\n\n"++
>   spaces 4++typeId ++ "RenCracker(k_) =\n" ++ 
>   spaces 6++typeId++"Cracker(k_) \n" ++
>   concat 
>    [spaces 8++"[["++id++"_int_Pick"++nr++"_"++typeId++".k_ <- m_ |\n" ++
>     spaces 12++"m_ <- make"++typeId++proc++nr++"("++id++", k_)]]\n" |
>        (nr,s,_) <- pickList, (a,proc,ls) <- agentLink, s==a, id <- ls]
>   ++"\n"++
>   spaces 4++"alpha"++typeId ++ "RenCracker(k_) =" ++
>   makeUnion 6
>    ("{|crack, tock|}" :
>     ["make"++typeId++proc++nr++"("++id++", k_)" |
>        (nr,s,_) <- pickList, (a,proc,ls) <- agentLink, s==a, id <- ls]) 
>  ++ "\n"

---------------------------------------------------------

Find first event of agent id in protocol.  Return message number, channel
name and message set name.

>firstEventSetChannel an id =
>  let (nr,a,b) = head [(nr,a,b) | (_, nr, a, b, _, _, _, _) <- protdesc an, 
>                                  Agent id==a || Agent id==b]
>  in if Agent id==a 
>     then if b==Environment then (nr, "env", "ENV_MSG") -- ("ENV_MSG"++nr, "env")
>          else (nr, "send", "OUTPUT_MSG") -- ("OUTPUT_MSG"++nr, "send") 
>     else if a==Environment then (nr, "env", "ENV_MSG") -- ("ENV_MSG"++nr, "env")
>          else (nr, "receive", "INPUT_MSG") -- ("INPUT_MSG"++nr, "receive")

Put Cracker and Monitor together in parallel

>makeMan1 typeId =
>  "    -- Put Cracker and Monitor together in parallel.\n\n"++
>  spaces 4++typeId++"ManSyncSet(n_) =\n"++
>  spaces 6++"inter(alpha"++typeId++"Cracker_r(n_), alpha"++
>     typeId++"RenMonitor(n_))\n\n"
>  ++
>  spaces 4++typeId++"Man1(n_) =\n"++
>  spaces 6++"let "++"Man1_0 =\n"++
>  spaces 12++typeId++"Cracker_r(n_)\n"++
>  spaces 12++"[| "++typeId++"ManSyncSet(n_) |]\n"++
>  spaces 12++typeId++"RenMonitor(n_)\n"++
>  spaces 10++"Man1_1 = Man1_0 \\ {manSync1_"++typeId++".n_}\n"++
>  spaces 6++"within chase(Man1_1)\n\n"
>  ++
>  spaces 4++"alpha"++typeId++"Man1(n_) =\n"++
>  spaces 6++"diff(\n"++
>  spaces 8++"union(alpha"++typeId++"Cracker_r(n_), alpha"++
>          typeId++"RenMonitor(n_)),\n"++
>  spaces 8++"{manSync1_"++typeId++".n_}\n"++
>  spaces 6++")\n\n"

>makeMan typeId =
>  "    -- Manager for all of "++typeId++".\n\n"++
>  spaces 4++typeId++"Manager =\n"++
>  spaces 6++"|| n_:"++typeId++" @ [alpha"++typeId++"Man1(n_)] "++
>    typeId++"Man1(n_)\n\n"
>  ++
>  spaces 4++"alpha"++typeId++"Manager =\n"++
>  spaces 6++"Union({alpha"++typeId++"Man1(n_) | n_ <- "++typeId++"})\n\n"

>makeTimedMan typeId =
>  "    -- Timed manager for all of "++typeId++".\n\n"++
>  spaces 4++typeId++"Manager =\n"++
>  spaces 6++"|| n_:"++typeId++" @ [alpha"++typeId++"RenCracker(n_)] "++
>  typeId++"RenCracker(n_)\n\n"
>  ++
>  spaces 4++"alpha"++typeId++"Manager =\n"++
>  spaces 6++"Union({alpha"++typeId++"RenCracker(n_) | n_ <- "++typeId++"})\n\n"

-----------------------------------------------------------------------
makeAllTypesKeyCompromiseManage
-----------------------------------------------------------------------

Manager for all types

>makeAllTypesKeyCompromiseManager :: Annotated -> Output
>makeAllTypesKeyCompromiseManager an =
>  let moduleName t = t++"CRACKING_M"
>  in 
>  "  -- Manager for all types.\n\n"++
>  "  Manager =\n  "++
>  spaces 2++makePar [(moduleName t++"::"++t++"Manager", 
>            moduleName t++"::alpha"++t++"Manager") | 
>              (t,_) <- crackables an]++"\n\n"++
>  "  AlphaManager = "++
>  makeUnion 4 [moduleName t++"::alpha"++t++"Manager" | (t,_) <- crackables an]++"\n"

-----------------------------------------------------------------------
makeParMonitorProcess
-----------------------------------------------------------------------

>makeParMonitorProcess typeId picks tolds internalFresh agentLink =  
>  let
>       procName arg2 = typeId++"Monitor(n_,"++arg2++")"
>	
>	monitoredAgents = [a | (_,a,_) <- (tolds++picks)]
>	knowsList =
>	  zip [1..] [(id,p++"_role") | (a,p,ls) <- agentLink, id <- ls,
>				member a monitoredAgents]
>  in
>     makeComment 4 (
>       procName "as_"++" monitors the foreground nonce n.  Its "++
>       "state is a set of (agent,role) pairs, reflecting which agents "++
>       "currently store n."++
>       "close.A.R event reflects the termination (or withdrawal) " ++  
>       "of agent A as role R, and therefore A (as R) forgets " ++ 
>       "all foreground values stored (including n).  " ++
>       procName "as_"++" updates accordingly; if no agents still "++
>       "hold n, then it synchronizes on manSync1_"++typeId++" with "++
>       typeId++"Cracker and/or "++typeId++"Recycler."
>     )++
>     "\n"++
>     maybeString internalFresh (
>	"    knows"++typeId++"(n_,X_,(a_,r_)) =\n" ++
>	spaces 6 ++ "if member((a_,r_),X_) then\n" ++
>	spaces 8 ++ "{s_ | s_ <- Set(F" ++ typeId ++"), member(n_,s_)}\n" ++
>	spaces 6++"else {s_ | s_ <- Set(F"++typeId++
>       "), not(member(n_,s_))}\n\n"
>     )++
>     "    "++procName "as_"++" =\n"++ 
>     maybeString internalFresh (
>       spaces 6 ++ "let\n" ++ 
>       (concat
>         [spaces 8 ++ "Knows" ++ show(n) ++ " = knows" ++ typeId ++
>          "(n_,as_,("++id++","++r++"))\n" | (n,(id,r)) <- knowsList]) ++
>       spaces 6 ++ "within\n" ++
>       spaces 8 ++ "agentKnows_" ++ typeId ++ 
>       (concat
>         ["?x_" ++ show n ++ ":Knows" ++ show n | (n,_) <- knowsList])
>       ++ " ->\n" ++
>       spaces 10 ++ "endSynch_" ++ typeId ++ 
>        " -> " ++ procName "as_" ++ "\n" ++
>        spaces 6 ++ "[]\n"
>     ) ++
>     spaces 6++
>     foldr1 (\ u v -> u++"\n"++spaces 6++"[] "++v)  ( -- distributeA 6 "[] "
>	[id++"_int_Pick"++nr++"_"++typeId ++".n_ ->\n" ++  
>	   spaces 11++procName ("union(as_,{("++id++","++p++"_role)})") |
>           (nr,s,_) <- picks, (a,p,ls) <- agentLink, s==a, id <- ls] ++
>	[id++"_int_Told"++nr++"_"++typeId++".n_ ->\n" ++
>          spaces 11++procName ("union(as_,{("++id++","++p++"_role)})") |
>            (nr,r,_) <- tolds, (a,p,ls) <- agentLink, r==a, id <- ls] ++
>	["close?a_?t_:roles(a_) ->\n" ++
>          "           if as_ =={(a_,t_)}\n"++ 
>          "           then manSync1_"++typeId++".n_ -> \n"++
>          spaces 18 ++ procName "{}" ++"\n"++
>          "           else "++procName "diff(as_,{(a_,t_)})"]
>     )++ "\n\n"



========================================================================
MANAGER PROCESSES
========================================================================

* party - list of all participants declared in the system which can
take on the role of an EXTERNAL process (i.e. not processes which are
declared to be internal).

>makeRoles agentLink =
>  let agentRoles =  [(a,r) | (_,r,as) <- agentLink, a <- as]
>      allAgents = remdups (map fst agentRoles)
>  in concat
>       ["  roles("++a++") = {"++
>        commaConcat [r++"_role" | (a',r) <- agentRoles, a'==a]++"}\n" |
>          a <- allAgents] ++
>     "  roles(_) = {}\n\n" -- for internal agents


* ordering - [([MsgNo], [(TypeName, [VarName])])]

* procId - list of tuples (id,proc) where id is the identity and proc
  is the corresponding process name of all processes which will be
  monitored by at least one manager process (used to determine the
  range for the close events of each monitor).

* Note: makeExternalManager is given the parameter "ordering" even
* though it is only relevent to the internal managers because they
* share the function "makeManMsgSets" (which needs this parameter in
* the case of the internal managers).

* "ordering" is used to store the ordering of fresh values introduced
by internal agents only.  This ordering is used in the spypick events
and the generation sets.  For example:

	[("1",[("Nonce",["na","nb"]),("Key",["kab"])])]

means that in message 1, the sender is an internal process and
introduces two fresh nonces na, nb, and one fresh key kab.  Thus in
the spypick event, we will have the ordering:

	spypick.(<na,nb>,<kab>)

where the Nonce Manager will synchronise with this and provide the two
nonces and the Key Manager will provide the fresh key.


Make parallel composition of some list of processes; first argument is list of
(process name, alphabet name) pairs

>makePar :: [(String, String)] -> String
>makePar [(p,_)] = p
>makePar ((p,a):pas) = replicate (length pas) '(' ++ p ++ makePar1 [a] pas

Add next stage to parallel composition.  First argument is list of alphabets
of those processes added so far.

>makePar1 :: [String] -> [(String, String)] -> String
>makePar1 _ [] = ""
>makePar1 as ((p,a):pas) = 
>  "\n    ["++makeUnionOneLine as++" || "++a++"] "++p++")"++makePar1 (a:as) pas


==================================================================
General Functions used for the Manager Process functions
==================================================================

------------------------------------------------------------------
linkProcAgents 
------------------------------------------------------------------

returns the list linking each process P defined in #Processes section
to all the corresponding agent identities that have been instanciated
to P in #System.  For example, 

     [("A","INITIATOR",["Alice","Bob"]),
      ("B","RESPONDER",["Bob"])]


>linkProcAgents :: Annotated -> [(String, ProcessName, [AgentId])]
>linkProcAgents an = linkProcAgents' an (procs an)

>linkProcAgents' :: Annotated -> [ProcessInfo] -> [(String, ProcessName, [AgentId])]
>linkProcAgents' _ [] = []
>linkProcAgents' an ((id,p,_,_,_):ps) =
>   let 
>      ls0 = map remLabel (actualAgents an)
>      ls = remdups(findAgentsId p ls0)
>   in
>     (id,p,ls):linkProcAgents' an ps
>   where
>     findAgentsId _ [] = []
>     findAgentsId p ((procName,id):ls) = 
>            if p==procName then 
>                 id:findAgentsId p ls
>            else
>                 findAgentsId p ls
>     remLabel (Star (name,(id:_))) = (name,id)
>     remLabel (SeqComp ((name,(id:_)):_)) = (name,id)

------------------------------------------------------------------
makeSpecificAccumList
------------------------------------------------------------------

>makeSpecificAccumList _ _ [] = []
>makeSpecificAccumList an typeId ((nr,(s,sl),(r,rl)):accList) =
>  let
>	isInternalRec = member r (intruderProcs an)
>	newSl = [v | v <- sl, (findtype an v)==typeId]
>	newRl = if isInternalRec then []
>	        else [v | v <- rl, (findtype an v)==typeId]
>	discard = (newSl==[]) && (newRl==[])
>  in
>	if discard then 
>	      makeSpecificAccumList an typeId accList
>	else
>	      (nr,(s,newSl),(r,newRl)):
>		makeSpecificAccumList an typeId accList

-----------------------------------------------------------------------
makeChannelDefs1
-----------------------------------------------------------------------

Channel declarations used in key compromise.
Parameter timedCracking is True iff we are doing timed key compromise
for this type, in which case some declarations can be left out.

>makeChannelDefs1 typeId picks tolds agentLink timedCracking  =
>  let	typeName = typeId
>  in 
>     "    -- Channel declarations used by " ++ typeId ++ "Monitor.\n\n"
>     ++
>     maybeString (not timedCracking) (
>        "    channel manSync1_" ++ typeId ++ " : " ++ typeName ++ "\n" ++
>	 "    channel manSync2_" ++ typeId ++ " : " ++ typeName ++"\n\n" ++
>        "    -- A_int_ToldNT.x represents that Agent A acquires the value\n"++
>        "    -- x of type T for the first time in message number N.\n\n" ++
>        concat
>          ["    channel "++id++"_int_Told"++nr++"_"++typeId++" : "++typeId++"\n" |
>             (nr,r,_) <- tolds, (a,_,ls) <- agentLink, id <- ls, r==a]
>     ) ++
>     "\n"++
>     "    -- The event A_int_PickNT.x represents that Agent A creates (or\n" ++
>     "    -- introduces) the fresh value x of type T in message number N.\n\n" ++
>     concat
>       ["    channel "++id++"_int_Pick"++nr++"_"++typeId++" : "++typeName++"\n" | 
>          (nr,s,_) <- picks, (a,_,ls) <- agentLink, id <- ls, s==a] ++
>     "\n"

------------------------------------------------------------------
distributeA
------------------------------------------------------------------

>-- distributeA n op ls = foldnlConcat n (map (\l -> op++l) ls)
>distributeA _ _ [] = ""
>distributeA n op [l] = spaces (n + length op) ++ l
>distributeA n op (l:ls) = 
>   spaces (n + length op) ++ l ++ "\n" ++ 
>                                         distributeA1 n op ls 
>   where
>     -- distributeA1 n op ls =    map (\l -> spaces n++op++l) ls
>     distributeA1 _ _ [] = ""
>     distributeA1 n op [l] = spaces n ++ op ++ l
>     distributeA1 n op (l:ls) = 
>       spaces n ++ op ++ l ++ "\n" ++ distributeA1 n op ls

