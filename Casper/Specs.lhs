Produce specifications and assertions

>module Specs(makeSpecs)
>where

>import Useful
>import Pprint
>import Atoms
>import Types
>import Messages
>import Annotated
>import Specs1
>import Specs2

>makeSpecs :: Annotated -> Output
>makeSpecs an =
>   (
>   if authinfo an == [] then ""
>   else
>    makeAuthSpecs an
>   )++
>   ifFlagString an GuessablesUsed 
>      "\n\nassert STOP [T= SYSTEM \\ diff(Events,{|INTRUDER_M::verify|})\n\n"

==========================================================================
Authentication specs

>makeAuthSpecs :: Annotated -> Output
>makeAuthSpecs an =
>   maybeString (hasFlag an UnboundedParallel && authinfo an /= []) (
>   heading "Authentication specifications" ++
>   "module AUTH_COMMON\n"++
>   "  createRenaming(factsRenaming) =\n"++
>   "    let rn = relational_image(factsRenaming)\n"++
>   "        dom = {a_ | (a_, _) <- factsRenaming}\n"++
>   "        extract({x_}) = x_\n"++
>   "    within \\ x_ @ if member(x_,dom) then extract(rn(x_)) else x_\n\n"++
>   "  -- The first argument is something of type createRenaming(X)\n"++
>   "  renameSet(f_, X_) =\n"++
>   "    {f_(x_) | x_ <- X_}\n"++
>   "  renameDeductions(rn_, ds_) =\n"++
>   "    {(rn_(f_), renameSet(rn_, fs_)) | (f_, fs_) <- ds_}\n\n"++    
>   "exports\n"++
>   "  -- Given a set of pairs (f, f') first compute the closure (but excluding\n"++
>   "  -- any facts in factsToRename) of the intruder's initial knowledge and then\n"++
>   "  -- rename all facts that appear in Deductions and LearnableFact.\n"++
>   "  RenameClosure(factsRenaming,factsToRename) = \n"++
>   "    let\n"++
>   "      rn_ = createRenaming(factsRenaming)\n"++
>   "      (IK_,ded_) =\n"++
>   "        INTRUDER_M::CloseButNotFacts_(\n"++
>   "          ALGEBRA_M::applyRenamingToSet(INTRUDER_M::IK0),\n"++
>   "          ALGEBRA_M::applyRenamingToDeductions(INTRUDER_M::Base_Deductions),\n"++
>   "          ALGEBRA_M::applyRenamingToSet(INTRUDER_M::KnowableFact),\n"++
>   "          factsToRename)\n"++
>   "      learnableFact = diff(INTRUDER_M::KnowableFact,IK_)\n"++
>   "    within\n"++
>   "      (renameDeductions(rn_,ded_), IK_, renameSet(rn_,learnableFact))\n\n"++
>   "  -- System to be used for checking authentication specifications\n"++
>   "  AUTH_SYSTEM(INTRUDER_0,IK) = \n"++
>   "    SYSTEM_M::SYSTEM_0\n"++
>   "    [| IntruderInterface |] INTRUDER_M::BUILD_INTRUDER'(INTRUDER_0,IK)\n\n"++
>   "endmodule\n\n")
>   ++
>   flatmap (makeSingleAuthSpec an) (authinfo an)

Make all assertions corresponding to single spec from input file

>makeSingleAuthSpec :: Annotated -> AuthInfo -> Output
>makeSingleAuthSpec an spec =
>  let realNames = allOfType an (findtype an a) \\ [intruderId an]
>      specName = "Authenticate" ++ procName an a ++ "To" ++ 
>                 procName an b ++ show authtype
>      -- authSpecName procs (n,(a,b,authtype))
>      moduleName = "AUTH"++show n++"_M"
>      (n,(a,b,authtype),authsigs) = spec
>  in
>  heading (" Authentication specification number "++show n)++
>  "module "++moduleName++"\n\n"
>  ++
>  (if hasFlag an UnboundedParallel then 
>    makeUnboundedParallelAuthModule an spec
>    ++
>    "  -- Specs for all agents being authenticated\n\n"++
>    "  "++specName++" =\n"++
>    makeAuthSpec_UP an spec++"\n\n"
>  else 
>    "  -- Spec parameterized by name of agent being authenticated\n\n"++
>    makeAuthSpec an spec
>    ++
>    "  -- Specs for particular agents being authenticated\n\n"++
>    concat
>     [makeSingleActualAuthSpec an realName spec |
>         -- form authentication specs for agents taking role a in protdesc
>       realName <- realNames]
>    ++
>    "  -- alphabet of specification\n\n" ++
>    "  alpha"++specName++" ="++
>    makeUnion 4
>      [alphaAuthName0 an (a,b,authtype)++"("++rn++")" | 
>         rn <- realNames] ++
>    "\n"
>    ++
>    "exports\n\n"
>    ++
>    "  -- Specs for all agents being authenticated\n\n"++
>    "  "++specName++" =\n    "++
>    makeParallel
>      [( particularAuthSpecName an (a,b,authtype) rn,
>         alphaAuthName0 an (a,b,authtype)++"("++rn++")" ) |
>            rn <- realNames]++"\n\n"
>  )
>  ++
>  "  -- System for authentication checking\n\n" ++
>  createAuthRenaming1 an spec specName
>  ++
>  "endmodule\n\n"++
>  -- Assertion
>  "assert "++moduleName++"::"++specName++" [T= \n"++
>  "       "++moduleName++"::SYSTEM_"++show n++"\n\n" 

=========================================================================
Make actual authentication specs and assertions for agent with name realName
in role given by a. 

>makeSingleActualAuthSpec :: Annotated -> String -> AuthInfo -> Output
>makeSingleActualAuthSpec an realName (n,(a,b,authtype),authsigs) =
>  let	pname = procName an a  -- role a is represented by process pname
>   -- number of runs agent realName can do in this role
>	count = sum [length pas + 1 | 
>                   SeqComp ((pn, a':_):pas) <- actualAgents an, 
>                   pn==pname, a'==realName]
>  in
>     "  "++particularAuthSpecName an (a,b,authtype) realName++
>     " =\n    " ++
>     interleave 
>       (isTimedAuth authtype) 
>       (copy (
>         authSpecName0 an (a,b,authtype)++"("++realName++
>         ")"
>       ) count) ++ 
>     "\n\n"

=========================================================================
Form parallel composition of processes, synchronizing on tock iff first
argument is True

>interleave :: Bool -> [String] -> String
>interleave False [] = "STOP"
>interleave True [] = "RUN({tock})"
>interleave False ps = foldr1 (\ p1 p2 -> p1++"\n  |||\n  "++p2) ps
>interleave True ps = 
>  foldr1 (\ p1 p2 -> "("++p1++"\n    [|{tock}|]\n    "++p2++")") ps

>makeParallel :: [(String, String)] -> String
>makeParallel [] = "STOP"
>makeParallel pas = fst (foldr1 makepar pas)
>  where makepar (p1,a1) (p2,a2) = 
>          ("("++p1++
>             "\n    [| inter("++a1++
>             ",\n             "++a2++") |]\n    " ++
>              p2 ++ ")", 
>           "union(" ++ a1 ++ ", " ++ a2 ++ ")")


=========================================================================

>particularAuthSpecName procs (a,b,at) realName =
>  "Authenticate" ++ procName procs a ++ realName ++ "To" ++ 
>  procName procs b ++ show at

>authParameter stale Aliveness = if stale then "True" else "False"
>authParameter _ WeakAgreement = "{}"
>authParameter _ (NonInjectiveAgreement _) = "{}"
>authParameter _ (Agreement _) = "{}"
>authParameter _ _ = "Not yet implemented"

=========================================================================

Rename so that agent1 does a running signal on message n1, and agent2 does a
commit signal on message n2

>createAuthRenaming1 :: Annotated -> AuthInfo -> String -> Output
>createAuthRenaming1 an (count,(a,b,authtype),((n1,agent1),(n2,agent2),ls)) specName = 
>  let
>       Annotated {
>           channels = (_,authC,directC)
>       } = an
>	time = isTimedAuth(getType(auths an!!(count-1)))
>       agreementFields = diffOneInstance ls [agent1,agent2]
>       agreementFieldsString = flatmap (\m -> "."++m) agreementFields
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>       -- information for running signal
>       (runs,runr,runm,run_se,run_re) = 
>         hd[(s,r,m,se,re) | (_,n,Agent s,Agent r,m,_,se,re) <- protdesc an, n==n1]
>	runSignal = 
>         "signal.Running"++show count++"."++role agent1++"_role."++
>         agent1 ++ (if hasFlag an UnboundedParallel && isAliveness authtype then "" else "."++agent2)++agreementFieldsString
>       clash_fields = run_se \\ atomsSend runm
>       run_re_renamed =
>         [ if elem v clash_fields then v++"_X_" else v | v <- run_re ]
>       runMsgs = 
>         let send =
>               "send."++runs++"."++runr++sessString++".ALGEBRA_M::rmb((Msg"++n1++", "++ 
>               showSenderMsg an runm++
>               ", <"++commaConcat run_se++">))"
>             comm = 
>               "comm."++runs++"."++runr++".ALGEBRA_M::rmb4((Msg"++n1++", "++ 
>               showSenderMsg an runm++", <"++
>               commaConcat run_se++">, <"++
>               commaConcat run_re_renamed++">))"
>         in (if isIn n1 directC && not (isIn n1 authC) then [send, comm] else [send])
>       messageSpaceRunnSet = "member((Msg"++n1++", "++  showSenderMsg an runm++ ", <"++commaConcat run_se++">),SYSTEM_M::OUTPUT_MSG" ++ n1 ++ ")"
>	runrange = varFields2 (
>                    runs:runr:run_se++
>                    (if isIn n1 directC then run_re_renamed else [])
>                  ) ++ senderFields runm
>       -- information for commit signal
>       (commits,commitr,commitm,commit_se,commit_re) =
>         hd[(s,r,m,se,re) | (_,n,s,r,m,(_,nn),se,re) <- protdesc an,n==n2]
>       commitSignal =
>         "signal.Commit"++show count++"."++role agent2++"_role."++
>         agent2 ++ "." ++ agent1 ++agreementFieldsString
>       commitMsgs =
>         if commits==Environment                      -- => Env -> agent2 
>         then [
>           "env."++agent2++".(Env"++n2 ++ ", " ++ 
>           showMsg an (receiverMsg commitm)++
>           ", <"++commaConcat commit_re++">)" ]
>         else if commitr==Environment                -- => agent2 -> Env
>         then [
>           "env."++agent2++".(Env"++n2 ++ ", " ++ 
>           showSenderMsg an commitm++
>           ", <"++commaConcat commit_se++">)" ]
>         else if (convert commits)==agent2         -- => agent2 -> commitr
>         then 
>           let send = 
>                 "send."++agent2++"."++convert commitr++sessString++
>                 ".ALGEBRA_M::rmb((Msg"++n2++", "++
>                 showSenderMsg an commitm++
>                 ", <"++commaConcat commit_se ++ ">))"
>           in [send] -- (if directC == All then [send, comm] else [send])
>         else [
> -- **** commit_s_extra
>            "receive."++convert commits++"."++convert commitr++sessString++
>	     ".ALGEBRA_M::rmb((Msg"++n2++", "++ 
>            showMsg an (receiverMsg commitm) ++
>	     ", <" ++ commaConcat commit_re ++ ">))" ]
>       messageSpaceCommSet =
>         if commits==Environment                      -- => Env -> agent2 
>         then ["member((Env"++n2 ++ ", " ++ showMsg an (receiverMsg commitm)++ ", <"++commaConcat commit_re++">),SYSTEM_M::ENV_INT_MSG" ++ n2 ++ ")" ]
>         else if commitr==Environment                -- => agent2 -> Env
>         then ["member((Env"++n2 ++ ", " ++  showSenderMsg an commitm++ ", <"++commaConcat commit_se++">),SYSTEM_M::ENV_INT_MSG" ++ n2 ++")" ]
>         else if (convert commits)==agent2         -- => agent2 -> commitr
>         then 
>           let send = 
>                 "member((Msg"++n2++", "++ showSenderMsg an commitm++ ", <"++commaConcat commit_se ++ ">),SYSTEM_M::OUTPUT_MSG" ++ n2 ++ ")"
>           in [send] -- (if directC then [send, comm] else [send])
>         else                                      -- => commits -> agent2 
>           ["member((Msg"++n2++", "++ showMsg an (receiverMsg commitm) ++ ", <" ++ commaConcat commit_re ++ ">),SYSTEM_M::INPUT_MSG" ++ n2 ++ ")"]
>       commitrange = 
>         if commits==Agent agent2 -- agent2 -> ???
>         then varFields2 (
>                convert commits:commit_se++
>		 (if commitr==Environment then [] else [convert commitr])
>	       )++senderFields commitm
>	     -- ??? -> agent2
>         else varFields2 (
>                convert commitr:commit_re++
>                --(if authC && commits/=Environment then
>                --   commit_se_renamed else [])++ 
>		 (if commits==Environment then [] else [convert commits])
>              )++receiver2Fields commitm
>       -- information for range
>       genVars = remdups(runrange++commitrange)
>       getType1 v = -- deal correctly with timestamps
>         let t = findtypeT an v in if t=="TS" then "TimeStamp" else t
>       renameTypes = remdups [getType1 v | Simple v <- genVars]
>  in "  SYSTEM_"++(show count)++" =\n"++
>        declareRenamedTypes renameTypes++
>        (if hasFlag an UnboundedParallel then 
>           "      AUTH_COMMON::AUTH_SYSTEM(INTRUDER_0,IK)"
>        else "      SYSTEM")
>        ++ "\n "
>     ++
>     "      [["++
>     commaNlConcat 8
>       [rM++" <-\n          "++runSignal | rM <- runMsgs] ++
>     ",  \n"++spaces 8++
>     commaNlConcat 8 
>       [ cM++" <-\n          "++commitSignal | cM <- commitMsgs ] ++
>     " |\n" ++ 
>     spaces 12++
>     format 12 ", " (makeVarGensRM an genVars) ++
>     ifFlagString an UnboundedParallel 
>       (",\n"++spaces 12++commaNlConcat 12 (remdups 
>       (("member("++agent1++",HONEST)"):messageSpaceRunnSet:messageSpaceCommSet)))
>     ++ 
>     sessString'++ "\n" ++
>     "      ]]\n"++
>       -- Done for effeciency as Sigma is large in Unbounded Parallel model
>     "      \\ "++if hasFlag an UnboundedParallel then "{| env, leak, send, receive"++
>       (maybeString (hasFlag an TimeUsed && not time) ", tock")++"|}\n\n"
>                  else "diff(Events, alpha"++specName++")\n\n"
>  where  -- chan s id = if s==id then "send." else "receive."
>	  role id = head [r | (a,r,_,_,_) <- procs an, id==a]
>	  getType (_,_,t) = t

Pretty-Prints the given message as a pattern, returning both the message and a
list of  equality constraints that must hold amonsgt the variables.
For instance, if the message was {x,k}{k} then this would be printed as
"{x,k}{k_2}"" and the constraint "k == k_1" would be included.

>showMsgAsPattern :: Annotated -> Msg -> (String, [String])
>showMsgAsPattern an msg =
>   let
>       showArgs vns (Sq ms) =
>           let (x,y,z) = showMsgs_ vns ms in (commaConcat x, y, z)
>       showArgs vns m = showMsg_ vns m
>
>       showMsgs_ :: [VarName] -> [Msg] -> ([String], [VarName], [String])
>       showMsgs_ usedVars [] = ([], usedVars, [])
>       showMsgs_ usedVars (m:ms) = 
>           let (m', usedVars', es1) = showMsg_ usedVars m
>               (ms', usedVars'', es2) = showMsgs_ usedVars' ms
>           in (m':ms', usedVars'', es1++es2)
>
>       vns v = [v++"_"++show i++"_" | i <- [2..]]
>
>       showMsg_ :: [VarName] -> Msg -> (String, [VarName], [String])
>       showMsg_ usedVars (Atom v) = 
>           let (vn, eqs) =
>                   if v `elem` usedVars then 
>                       let vn = head ([vn | vn <- vns v, not (vn `elem` usedVars)])
>                       in (vn, [vn++" == "++ v])
>                   else (v, [])
>           in (if findtype an v == "TimeStamp" then "Timestamp."++vn else vn,
>                    vn:usedVars, eqs)
>       showMsg_ usedVars (Encrypt k ms) = 
>           let (msg1, uvs1, es1) = showMsg_ usedVars k
>               (msgs, uvs2, es2) = showMsgs_ uvs1 ms
>           in ("Encrypt.(" ++ msg1 ++ ", <" ++ commaConcat msgs ++ ">)", uvs2, es1++es2)
>       showMsg_ usedVars (Sq ms) =
>           let (ms', usedVars', es) = showMsgs_ usedVars ms
>           in ("Sq.<" ++ commaConcat ms' ++ ">", usedVars', es)
>       showMsg_ usedVars (Xor m m') =  
>           let (msg1, uvs1, es1) = showMsg_ usedVars m
>               (msg2, uvs2, es2) = showMsg_ uvs1 m'
>           in ("Xor.(" ++ msg1 ++ ", " ++ msg2 ++ ")", uvs2, es1++es2)
>       showMsg_ usedVars (Undec m _) = showMsg_ usedVars m
>       showMsg_ usedVars (Forwd _ m) = showMsg_ usedVars m
>       showMsg_ usedVars (Apply f m) | isHashFunction (fnts an) f =
>           let (ms, uvs, es) = showArgs usedVars m
>           in ("Hash.("++f++", <"++ms++">)", uvs, es)
>       showMsg_ usedVars (Apply f m) =
>           case findFnType1 (fnts an) f of
>               Symb dom r ->
>                   let (ms, uvs, es) = showArgs usedVars m
>                   in (f++"__.("++ms++")", uvs, es)
>       showMsg_ usedVars (Sent m ms) =
>           let (msg1, uvs1, es1) = showMsg_ usedVars m
>               (ms', uvs2, es2) = showMsgs_ uvs1 ms
>           in ("Sent.(" ++ msg1 ++ ", <" ++ commaConcat ms'++ ">)", uvs2, es1++es2)
>
>       (s, _, cs) = showMsg_ [] msg
>   in (s, cs)

>makeUnboundedParallelAuthModule :: Annotated -> AuthInfo -> Output
>makeUnboundedParallelAuthModule an (n,(a,b,authtype),((n1,agent1),(n2,agent2),ls)) = 
>   let
>       sentmsg = hd [sentmsg | (_,sentmsg,_,_,_,n) <- sentrep an, n == n1]
>       -- We explicity conver the message into a senderMsg as showSenderMsg does not
>       -- properly display the sent message tags (it shows them from a senders POV
>       -- rather than a receivers as it should. FIXME)
>       (sentmsgString, eqConstraints) = showMsgAsPattern an (senderMsg sentmsg)
>       timestampsInMessage = filter (\ x -> findtypeT an x == "TS") (atoms m)
>           where Sent m _= sentmsg
>       useTimestampedFacts = hasFlag an TimestampsUsed && isTimedAuth authtype
>       role id = head [r | (a,r,_,_,_) <- procs an, id==a]
>       agreementFields = diffOneInstance ls [agent1,agent2]
>       agreementFieldsString = flatmap (\m -> "."++m) agreementFields
>       agreementFieldsTypeString = flatmap (\m -> "."++findtype an m) agreementFields
>       runSignalFields = agent1++(if isAliveness authtype then "" else "."++agent2)++
>           agreementFieldsString
>       -- string x to appear in the form signal.x
>       runSignal = "Running"++show n++"."++role agent1++"_role."++runSignalFields
>       -- string that sentmsgString gets renamedto
>       renamedSentMsg = "AuthTaggedSignals"++show n++".TRunning"++show n++"."++
>           (maybeString useTimestampedFacts ("<"++commaConcat timestampsInMessage++">."))++runSignalFields++".tag_"
>       externalAgent2s = remdups [(agent,vs) | SeqComp as <- actualAgents an, (pn, agent:vs) <- as,
>                                         pn==procName an agent2]
>       -- The list of free variables that are both generated by agent2 and
>       -- occur in sentmsg. These are used for ensuring that we do not rename
>       -- sent messages between an internal agent and an external agent.
>       externalAgent2GeneratedVars = 
>           intersection (concat [gen | (a,_,_,_,gen) <- procs an, agent2==a]) vs
>           where 
>               Sent _ ms = sentmsg
>               vs = [v | Atom v <- ms]
>       -- List of tuples of type [TaggedSignals, Restriction] corresponding
>       -- to renamings of a sentmsgstring to TaggedSignal whenever restriction holds.
>       makeRenamingsAndRestrictions = (varsStr++".Internal", res):rest
>           where
>               varsStr = "TRunning"++show n++"."++
>                   (maybeString useTimestampedFacts ("<"++commaConcat timestampsInMessage++">."))++
>                   runSignalFields
>               res = if rest /= [] then "not(("++(opConcat ") or (" . map snd) rest ++"))" else ""
>               -- we must remove dupes otherwise the same fact is renamed to several 
>               -- different things
>               rest = (filter ((/=) "" . snd). remdupsf snd . map make . zip externalAgent2s) [1..]
>               agent2fvts = concat [tail vs | (id,_,vs,_,_) <- procs an, id==agent2]
>               make ((agent, args), i) = (varsStr++".External"++show i, res)
>                   where res = opConcat " and " (filter (/="") (zipWith makeMember args agent2fvts))
>               makeMember arg fv = if elem fv vs then "member("++fv++",{"++arg++"})" else ""
>               Sent _ ms = sentmsg
>               vs = [v | Atom v <- ms]
>       -- Set of tuples of the form (sentmsgstring, TaggedSignal) for renamings
>       makeRenamingSet ind runningFact restriction = 
>           "{("++sentmsgString++", AuthTaggedSignals"++show n++"."++runningFact++")\n"++
>           spaces ind++"| "++sentmsgString++" <- FACTS_TO_RENAME"++
>           (if eqConstraints /= [] then ",\n"++spaces (ind+2)++commaConcat eqConstraints else "")++
>           if restriction /= "" then ",\n"++spaces ind++"  "++restriction++"}"
>           else "}"
>       -- String giving a restriction on the free vars in the running signal to 
>       -- constrain the signals to agents we are interested in.
>       renamingRestriction = (commaConcat . filter (/="") . map makeRestriction)
>               (agent1:agent2:(intersection externalAgent2GeneratedVars (authArgs authtype)))
>           -- We're only interested in authentication attacks against external agents
>           -- with an honest internal agent.
>           where 
>               makeRestriction var = 
>                   if var == agent1 then "member("++var++",inter("++findtype an var++",HONEST))"
>                   -- We enforce no restrictions if it's an aliveness test as we do not 
>                   -- mind who agent2 is, just that agent1 is alive.
>                   else if isAliveness authtype then ""
>                   -- Otherwise, we want the agent to be an external agent (as we are authenticating
>                   -- to agent2, and agent2 is ALWAYS external (this should be typechecked)).
>                   else if var == agent2 then 
>                       "member("++var++", {"++(commaConcat . remdups . map fst) externalAgent2s++"})"
>                   -- ... and all variables of agent2's should thus be external values.
>                   else "member("++var++",{"++commaConcat (remdups (
>                       allofSubtypeTypeStatus an (findtype an var) [] External))++"})"
>   in
>      "  -- Set of all facts that would be renamed to signals in infer events\n"++
>      "  FACTS_TO_RENAME = \n"++
>      "    {"++sentmsgString++" | \n"++
>      "      "++sentmsgString++" <- INTRUDER_M::KnowableFact}\n\n"++
>      "  -- Set of tuples of the form (Fact, RunningFact) that is used to create a\n"++
>      "  -- renaming function of type Fact -> RunningFact.\n"++
>      "  FACT_RENAMING ="++
>      makeUnion 4 [makeRenamingSet 6 rf res | (rf,res) <- makeRenamingsAndRestrictions]++"\n"++
>      "  (RenamedDeductions_,IK,RenamedLearnableFact) =\n"++
>      "    AUTH_COMMON::RenameClosure(FACT_RENAMING,FACTS_TO_RENAME)\n\n"++
>      "  -- Build the basic (non-chased) intruder by renaming all the infer.(f,fs)\n"++
>      "  -- events corresponding to the messages that should be renamed.\n"++
>      "  INTRUDER_0 = \n"++ 
>      "    INTRUDER_M::INTRUDER_00(RenamedDeductions,RenamedLearnableFact)\n" ++
>      "      [[infer.("++renamedSentMsg++",fs_) <-\n"++
>      "         signal."++runSignal++"\n"++
>      "        | ("++renamedSentMsg++", fs_) <- RenamedDeductions"++
>      (if renamingRestriction /= "" then ",\n          "++renamingRestriction++"\n" else "\n")++
>      "      ]] \\ {|infer"++(ifFlagString an TimestampsUsed ",INTRUDER_M::tockInfer")++"|}\n\n"++
>      "exports\n"++
>      "  RenamedDeductions = RenamedDeductions_\n\n"++
>      "  -- Datatypes below are what facts are renamed in in FACT_RENAMING above\n"++
>      "  datatype Tag"++show n++" = "++"Internal"++
>           (flatmap (\ i -> " | External"++show i) [1..length externalAgent2s])++"\n"++
>      "  datatype TaggedSignals"++show n++" = TRunning"++show n++
>           (maybeString useTimestampedFacts ".Seq(TS)")++".ALL_PRINCIPALS"++
>           (if isAliveness authtype then "" else ".ALL_PRINCIPALS")++
>           agreementFieldsTypeString++".Tag"++show n++"\n\n"

