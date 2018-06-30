Produce process definitions for honest agents

>module Agents(processDefs) where

>import Useful
>import Pprint
>import Atoms
>import Annotated
>import Messages
>import Types
>import SecureChannels

>processDefs :: Annotated -> [SessionId] -> Output
>processDefs an sessids = 
>       maybeString (auth /= Some []) bufferDef ++
>       flatmap (processDef an sessids) (procs an)
>   where Annotated {channels = (_,auth,_)} = an

======================================================================
Definition of a buffer

>bufferDef :: String
>bufferDef = 
>  "  -- A buffer between honest agents\n\n"++
>  "  BUFF(in_, out_, data_, cap_) =\n"++
>  "    let \n"++
>  "      in_data = {output_proj(x_) | x_ <- data_}\n"++
>  "      BUFF_0(ms_) =\n"++
>  "        SKIP\n"++
>  "        []\n"++
>  "        in_?(l_,m_,_):in_data ->\n"++
>  "          ( if #ms_ < cap_ then BUFF_0(ms_^<(l_,m_)>) else error -> STOP )\n"++
>  "        []\n"++
>  "        ms_ != <> & \n"++
>  "          [] (l_,m_,se_,re_) : data_, (l_,m_) == head(ms_) @\n"++
>  "            out_!ALGEBRA_M::rmb((l_,m_,re_)) -> BUFF_0(tail(ms_))\n"++
>  "    within BUFF_0(<>)\n\n"

======================================================================

Produce process definition for one agent

>processDef :: Annotated -> [SessionId] -> ProcessInfo -> Output
>processDef an sessids (id,name,args,_,_) =
>   let 
>       args' = if hasFlag an TimeUsed then "runTimeRemaining_":args else args
>       (outputs,_) = 
>           processNextStep an endingType id name "" args' 1 0 firstNr sessids_init sessids_resp True
>       firstNr = head[nr | (_,nr,s,r,_,_,_,_) <- protdesc an,
>			  s==Agent id || r==Agent id]
>       endingType = if hasFlag an CrackablesUsed
>                  then "close." ++ id ++ "." ++ name ++ "_role -> SKIP"
>                  else "SKIP"
>       sessids_init = remdups [(m,n) | (_,(_,a,_,n,ms),_) <- sessids, m <- n:ms, a==id]
>       sessids_resp = remdups [(m,n) | (_,(_,a,_,n,ms),_) <- sessids, m <- n:ms]
>       -- add the session ids (for session initialisation) to the arguments
>       args'' = args' ++["c" ++ n | (n,n') <- sessids_init, n==n']
> in "  -- " ++ name ++ "\n\n" ++
>    -- show allinfo ++ "\n" ++
>    "  "++name ++ "_0"++showArgs args''++ " =\n" ++ 
>    outputs ++ "\n" ++ 
>    processRename an (id, name, args'')

Print arguments in parentheses, separated by commas

>showArgs :: [String] -> String
>showArgs args = "(" ++ commaConcat args ++ ")"

>name' :: String -> Int -> String
>name' name p = name ++ "_0" ++ copy '\'' p

======================================================================

Produce next step of process definition, then iterate

** Do we need to return args? **
The argument `skips' represents the number of outstanding "else SKIP"s.  The
argument `primes' represents the number of primes that should appear on the
next process name.

>processNextStep :: Annotated -> String -> AgentId -> ProcessName -> Output -> 
>   [Argument] -> Int -> Int -> String -> [(String,String)] -> 
>   [(String,String)] ->  Bool -> (Output, [Argument])
>processNextStep an = processNextStep' an (protdesc an)

>processNextStep' :: Annotated -> ProtDesc' -> String -> AgentId -> ProcessName -> 
>   Output -> [Argument] -> Int -> Int -> String -> [(String,String)] -> 
>   [(String,String)] ->  Bool -> (Output, [Argument])
>processNextStep' _ [] endingType _ _ os args _ aborts _ _ _ _ =
>   (os++"    "++endingType++concat (copy ")" aborts)++"\n", args)
>processNextStep' an (m:ms) endingType id name os args primes aborts firstNr 
>       sessids_init sessids_resp firstMsg = 
>  let (os', args', primes', aborts',firstMsg') = 
>        processStep an endingType id name args primes aborts firstNr m 
>           sessids_init sessids_resp firstMsg
>  in processNextStep' an ms endingType id name (os ++ os') args' primes' aborts' 
>       firstNr sessids_init sessids_resp firstMsg'

======================================================================
Produce single step for this agent

>processStep :: Annotated -> String -> AgentId -> ProcessName ->
>   [Argument] -> Int -> Int -> String -> ProtMsgDesc' -> [(String,String)] -> 
>   [(String,String)] -> Bool -> (Output, [Argument], Int, Int, Bool)
>processStep an endingType id name args primes aborts firstNr 
>   (assigns, no, sender, receiver, msg, test, se, re) sessids_init sessids_resp firstMsg
>  | Agent id == sender
>      = processSenderStep an id name args primes aborts receiver assigns no msg 
>           sessids_init sessids_resp se firstMsg
>  | Agent id == receiver  
>      = processReceiverStep an endingType id name args primes aborts 
>           sender firstNr no msg sessids_resp test re firstMsg
>  | otherwise
>      = ("", args, primes,aborts,firstMsg)

======================================================================
Produce next bit of process definition if agent sends this message

>processSenderStep :: Annotated -> AgentId -> ProcessName -> [Argument] ->
>   Int -> Int -> Player -> AssignmentList -> MsgNo -> Msg -> 
>   [(String,String)] -> [(String,String)] -> [VarName] -> Bool -> 
>   (Output, [Argument], Int, Int, Bool)
>processSenderStep an id name args primes aborts receiver assigns no msg 
>       sessids_init sessids_resp se firstMsg =
>   let	
>       newVars = map fst assigns
>       args' = args ++ newVars
>       dtnames = [tn | (tn,_,_) <- dtdefs an]
>       usesDTs = -- does this message use any datatype?
>           anyOfTypes (fvts an) (fnts an) dtnames msg
>       timestamps = senderTimeStamps (fvts an) (fnts an) msg \\ args
>       tripleString = -- string to represent triple
>           (case receiver of Agent _ -> "(Msg"; Environment -> "(Env")++
>           no++", " ++ showSenderMsg an msg++",<" ++ 
>           commaConcat se++">)"
>       eventHeader = -- first few fields of event
>           case receiver of 
>               Agent r -> 
>                   if no `elem` [m | (_,2,ms) <- sessinfo an, m <- ms] then
>                       if (no,no) `elem` sessids_init then
>                           let cno = head [head ms | (_,2,ms) <- sessinfo an, no `elem` ms] in
>                           if no == cno then
>                               "output."++id++"."++r++".c"++no
>                           else
>                               "pair.c" ++ cno ++ ".c" ++ no ++ " -> output."++id++"."++r++".c"++no
>                       else if no `elem` (map fst sessids_init) then
>                               let cno = head (map snd (filter ((== no) . fst) sessids_init)) in
>                               "output."++id++"."++r++".c"++cno
>                           else if no `elem` (map fst sessids_resp) then
>                               let cno = head (map snd (filter ((== no) . fst) sessids_resp)) in
>                               "output."++id++"."++r++".c"++cno
>                           else "output."++id++"."++r
>                       else
>                           if (no,no) `elem` sessids_init then
>                               "output."++id++"."++r++".c"++no
>                           else if no `elem` (map fst sessids_init) then
>                               let cno = head (map snd (filter ((== no) . fst) sessids_init)) in
>                               "output."++id++"."++r++".c"++cno
>                           else if no `elem` (map fst sessids_resp) then
>                               let cno = head (map snd (filter ((== no) . fst) sessids_resp)) in
>                               "output."++id++"."++r++".c"++cno
>                           else "output."++id++"."++r
>               Environment -> "env_I." ++ id
>       messageSetName = -- set that tripleString should be from
>           case receiver of
>               Agent _ -> "OUTPUT_INT_MSG"++no
>               Environment -> "ENV_INT_MSG"++no
>       eventString1s = -- guarded event, without choices
>           if (usesDTs || hasFlag an UnboundedParallel) then 
>               ["member("++tripleString++", "++messageSetName++") & ",
>                   eventHeader ++ "."++tripleString++" ->\n"]
>         else [eventHeader ++ "."++tripleString++" ->\n"]
>       choicesString = concat["[] "++ts++" : TS @ " | ts <- timestamps]
>       eventString = "    "++
>           if timestamps == [] then format 4 "" eventString1s
>           else format 6 "" (choicesString : eventString1s)
>       nextname = name' name
>       sessidsArgs = ["c" ++ n | (n,n') <- sessids_init, n==n']
>   in
>       if assigns == [] then 
>           (eventString, args++timestamps, primes, aborts,False)
>       else 
>           ("    "++nextname primes++
>            showArgs(args++[snd(hd assigns)]++sessidsArgs)++
>               concat (copy ")" aborts)++"\n\n"++ 
>               -- New processes, doing assignments one by one
>               concat [
>                 "  "++nextname(primes+length ves-2)++
>                 showArgs(args ++ map fst (init ves)++sessidsArgs)++" =\n  "++
>                 nextname(primes+length ves-1)++
>                 showArgs(args++map fst (init ves)++[snd (last ves)]++
>                          sessidsArgs)++"\n\n" |
>                   ves <- tl (tl(inits assigns))] ++
>               -- Final new process, which actually does an event
>               nextname(primes+length assigns-1)++
>               showArgs(args ++ newVars++sessidsArgs)++" =\n"++ 
>               eventString,
>          args'++timestamps, primes + length assigns, 0,False)

======================================================================
Produce next bit of process definition if agent receives this message

>processReceiverStep :: Annotated -> Output -> AgentId -> ProcessName -> [Argument] ->
>   Int -> Int -> Player -> String -> MsgNo -> Msg -> 
>   [(String,String)] -> Test -> [VarName] -> Bool -> 
>   (Output, [Argument], Int, Int, Bool)
>processReceiverStep an endingType id name args primes 
>       aborts sender firstNr no msg sessids_resp (teststring, hastest) 
>       re firstMsg =
>   let 
>       senderIds = [Simple s | Agent s <- [sender]]
>       msgFields = remdupsmerge senderIds (receiverFields msg)
>       newargs = [a | Simple a <- msgFields, isNew a] ++
>                   [a | Subst a _ <- msgFields, isNew a] -- ++ newkeys
>       isNew a = not (member a args)
>       args' = args ++ newargs
>       dtnames = [tn | (tn,_,_) <- dtdefs an]
>       usesDTs = -- does this message use any datatype?
>           anyOfTypes (fvts an) (fnts an) dtnames msg
>       eventHeader = -- first few fields of event
>           case sender of
>               Agent s -> 
>                   if (no,no) `elem` sessids_resp then
>                        "input." ++ s ++ "." ++ id ++ ".c" ++ no
>                   else if no `elem` (map fst sessids_resp) then
>                        let cno = head (map snd (filter ((== no) . fst) sessids_resp)) in
>                        "input."++s++"."++id++".c"++cno
>                   else
>                        "input."++ s ++"."++ id
>               Environment -> "env_I." ++ id
>       extraString = -- string representing extras
>           ",<" ++commaConcat re++ ">"
>       tripleString = -- string to represent triple
>           (case sender of Agent _ -> "(Msg"; Environment -> "(Env")++
>          no++", "++showReceiverMsg an msg ++extraString ++")"
>       messageSetName = -- set that tripleString should be from
>           case sender of
>               Agent _ -> "INPUT_INT_MSG"++no
>               Environment -> "ENV_INT_MSG"++no
>       (aborts',withdrawString) = 
>	        if hasFlag an Withdraw && {- sender/=Environment && -} firstNr/=no then 
>               (aborts, "    " ++ endingType ++ "\n"++"   []\n")
>           else (aborts,"")
>       choicesString = 
>           case sender of
>               Agent _ -> 
>                   format 4 "" (
>                       -- symmetric sessions
>                       (if no `elem` [m | (_,2,ms) <- sessinfo an, m <- ms] then
>                           if (no,no) `elem` sessids_resp then
>                               if no /= head [head ms | (_,2,ms) <- sessinfo an, no `elem` ms] then
>                                   let cno = head [head ms | (_,2,ms) <- sessinfo an, no `elem` ms]
>                                   in
>                 	                ["[] c" ++ no ++ " : SessionId(Msg" ++ no ++ ") @ pair.c" ++ cno ++ ".c" ++ no ++ " -> "]
>                               else ["[] c" ++ no ++ " : SessionId(Msg" ++ no ++ ") @ "]
>                           else [""]
>                       -- other sessions
>                       else if (no,no) `elem` sessids_resp then 
>                           ["[] c" ++ no ++ " : SessionIds @ "] 
>                       else [""])
>                   ++
>                   [let t = findtype an a in
>                       "[] "++a++" : "++(
>                       if t=="TimeStamp" then "TS" 
>                       else t)++" @ "
>                   | Simple a <- msgFields, isNew a] ++
>                   ["[] "++a++" : " ++typeSet an a m ++ " @ "
>                   |  Subst a m <- msgFields, isNew a])
>               Environment -> 
>                   format 4 "" (
>                       -- For each choice of the variables in the sender message
>                       -- that gets swallowed up by % notation (i.e. senderFields
>                       -- that are not receiverFields).
>                       [let t = findtype an a in
>                           "[] "++a++" : "++(
>                           if t=="TimeStamp" then "TS" 
>                           else t)++" @ "
>                       | Simple a <- remdups (senderFields msg) \\ msgFields, isNew a] ++
>                       [let t = findtype an a in
>                           "[] "++a++" : "++(
>                           if t=="TimeStamp" then "TS" 
>                           else t)++" @ "
>                       | Simple a <- msgFields, isNew a] ++
>                       ["let "++a++" = " ++showSenderMsg an m++ " within "
>                       | Subst a m <- msgFields, isNew a]) 
>       eventString1s = -- event without choices, guarded for use of DTs
>           if (usesDTs || (hasFlag an UnboundedParallel && (choicesString /= []))) then 
>               ["member("++tripleString++", "++messageSetName++") & ",
>               eventHeader ++ "."++tripleString++" ->\n"]
>           else [eventHeader ++ "."++tripleString++" ->\n"]
>       eventString2s = -- event without choices, guarded by tests
>           if teststring == "" then eventString1s 
>           else (teststring++" & ") : eventString1s
>       eventString =
>           if choicesString /= "" then 
>               "    " ++ format 6 "" (choicesString:eventString2s)
>           else "    "++format 4 "" eventString2s
>       nextname = name' name primes
>       updateTimestamp arg =
>           if arg == "runTimeRemaining_" then if not firstMsg then arg++"-1" else arg
>           else if hasFlag an TimestampsUsed then
>               if findtype an arg == "TimeStamp" then "dects("++arg++")" else "updt("++arg++")"
>           else arg
>       nextProc = nextname++showArgs (map updateTimestamp args)
>   in 
>       -- Allow a tock between the receiving event, if timeUsed
>       if hasFlag an TimeUsed then
>           ("      "++nextname++showArgs(args)++"\n\n"++
>           "  "++nextname++showArgs(args)++" = \n"++
>           "    tock -> "++(if not firstMsg then 
>                               "(if runTimeRemaining_ < 0 then SKIP\n"++
>                               "      else "++nextProc++")\n"
>                           else nextProc++"\n")++
>           "    [] \n"++withdrawString++eventString,
>           args',primes+1,aborts',False)
>       else (withdrawString++eventString, args', primes, aborts',False)

======================================================================
Apply renaming

>processRename an (id, name, args) 
>  | not (hasFlag an TimeUsed)
>  = bufferedProcDef++
>    "  "++name'++" =\n"++"    "++name1++"\n"++renamingString 
>    ++
>    ifFlagString an TimedAuth (
>      "  TIMED_"++ name' ++ " =\n" ++
>      "    "++name1++"\n"++renamingString
>   )
>  | hasFlag an TimeUsed
>  = bufferedProcDef++
>    "  "++name'++" =\n"++
>    "    "++name1++"\n"++renamingString
> where
>   Annotated {channels=(_,auth,direct), protdesc=protdes} = an
>   name' = name++showArgs args
>   name0 = name++"_0"++showArgs args
>   name1 = name++"_1"++showArgs args
>   bufferedProcDef = 
>     "  "++name1++" = "++
>     if auth /= Some [] then "\n"++"    "++makeBufferedProcDef an id name0 auth
>     else name0++"\n\n"
>   sessString = if sessinfo an /= [] then ".c_" else ""
>   sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>   renamingString =
>    "      "++
>    nlConcat 6 (
>    -- inputs on non-direct, or authenticated channels
>      ["[[input."++s++"."++id++sessString++".(l_,m_,re_)"++" <- "++
>       "receive."++s++"."++id++sessString++".ALGEBRA_M::rmb((l_,m_,re_))"++" |\n"++ 
>       "          "++s++" <- "++findtype an s++", "++
>       "(l_,m_,se_,re_) <- INT_MSG_INFO" ++n++sessString'++"]]" |
>       (_,n,Agent s, Agent r,_,_,_,_) <- protdes, r == id, 
>                                         not (isIn n direct) || isIn n auth]
>    ++
>    -- inputs on direct && not authenticated channels
>      ["[["++
>       let input = "input."++s++"."++id++".(l_,m_,re_)" in 
>       input++" <- receive."++s++"."++id++".ALGEBRA_M::rmb((l_,m_,re_))"++",\n"++
>       "        "++input++" <- comm."++s++"."++id++".ALGEBRA_M::rmb4((l_,m_,se_,re_))"++" |\n"++ 
>       "          "++s++" <- "++findtype an s++", "++
>       "(l_,m_,se_,re_) <- INT_MSG_INFO" ++n++"]]" |
>       (_,n,Agent s, Agent r,_,_,_,_) <- protdes, r == id, 
>                                         isIn n direct && not (isIn n auth)]
>    ++
>    -- outputs on authenticated channels and normal channels
>      ["[[output."++id++"."++r++sessString++".(l_,m_,se_)"++" <- "++
>       "send."++id++"."++r++sessString++".ALGEBRA_M::rmb((l_,m_,se_))"++" |\n"++ 
>       "          "++r++" <- "++findtype an r++", "++
>       "(l_,m_,se_,re_) <- INT_MSG_INFO"++n++sessString'++"]]" |
>       (_,n,Agent s, Agent r,_,_,_,_) <- protdes, s == id, 
>                                         isIn n auth || not (isIn n direct)]
>    ++
>    -- outputs on direct channels
>    -- *** we ought only to output on one of comm/send to the intruder...
>    -- but to make this code simpler, we block it by not including
>    -- comm.A.Mallory events in the process alphabet.
>      ["[["++
>       let output = "output."++id++"."++r++".(l_,m_,se_)" in
>       output++" <- send."++id++"."++r++".ALGEBRA_M::rmb((l_,m_,se_)),\n"++
>       "        "++output++" <- comm."++id++"."++r++".ALGEBRA_M::rmb4((l_,m_,se_,re_)) |\n"++ 
>       "          "++r++" <- "++findtype an r++", "++
>       "(l_,m_,se_,re_) <- INT_MSG_INFO"++n++"]]" |
>       (_,n,Agent s, Agent r,_,_,_,_) <- protdes, s == id, 
>                                         not (isIn n auth) && isIn n direct]
>    ++
>    -- messages from the environment
>      ["[[env_I."++id++".m_ <- env."++id++".ALGEBRA_M::rmb(m_) |\n"++
>       "          m_ <- ENV_INT_MSG"++n++"]]" |
>       (_,n,Agent s, Environment,_,_,_,_) <- protdes, s == id]
>    ++
>      ["[[env_I."++id++".m_ <- env."++id++".ALGEBRA_M::rmb(m_) |\n"++
>       "          m_ <- ENV_INT_MSG"++n++"]]" |
>       (_,n,Environment,Agent s, _,_,_,_) <- protdes, s == id]
>    )++"\n\n"

Add buffering on output channels

>makeBufferedProcDef an id name0 auth = 
>  let -- calculate other guys we send messages to
>      idns =
>        [(b,n) | (_,n,Agent a, Agent b, _, _,_,_) <- protdesc an, a == id,
>                                                              isIn n auth]
>      ids = remdups(map fst idns)
>      id_ns_s = [(b, [n | (b',n) <- idns, b==b']) | b <- ids]
>  in 
>  if ids==[] then name0++"\n\n"  
>  else
>    "let "++
>    (nlConcat 8 . concat)
>      [let bType = findtype an b in
>       ["-- buffering to "++b,
>        "data_"++b++" = "++makeUnionOneLine ["INT_MSG_INFO"++n | n <- ns],
>        -- following item necessary for FDR3, but will cause problems to FDR2
>        "BUFF_"++b++" :: (Encryption) -> Proc", 
>        "BUFF_"++b++"("++b++") = BUFF(output."++id++"."++b++
>           ", receive."++id++"."++b++", data_"++b++", 1)", -- **** not nec 1
>        "alphaB_"++b++"("++b++") =",
>        "  {output."++id++"."++b++".output_proj(x_), receive."++
>          id++"."++b++".rmb_input_proj(x_) | x_ <- data_"++b++"}",
>        "BUFFS_"++b++" = || "++b++" : inter(HONEST, "++bType++
>          ") @ [alphaB_"++b++"("++b++")] BUFF_"++b++"("++b++")",
>        "alphaBs_"++b++" = Union({alphaB_"++b++"("++b++") | "++
>           b++" <- inter(HONEST, "++bType++")})"
>       ] | 
>          (b,ns) <- id_ns_s] 
>    ++"\n"++
>    "    within\n"++
>    "      "++name0++"\n"++
>    "      [| inter({|output|}, "++makeUnionOneLine ["alphaBs_"++b  | b <- ids]++") |]\n"++
>    "      ("++foldr1 interleave ["BUFFS_"++b | b <- ids]++")\n\n"
>    where interleave xs ys = xs++" ||| "++ys
