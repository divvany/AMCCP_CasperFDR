Helping functions for the UnboundParallel Implementation

>module UnboundParallel(
>  playerAtom, makeSentRep, SentRep, factsFromSentRep,
>  makeSentDeductions, makeProcParameters,
>  generateSystem
>) where


>import Useful
>import Pprint
>import Atoms
>import Annotated
>import Messages
>import Types
>import Maybe1
>import List (sort)

Converts a player to the respective Atom, as it would be used in messages.

>playerAtom:: Player -> Msg
>playerAtom Environment = (Atom "ENV")
>playerAtom (Agent x) = (Atom x)

Extract the simple atoms of a message as they are seen by the receiver of the
message. As the receiver cannot decode a "Undec"-message, it is not changed.

>receiverSimpleAtoms :: Msg -> [Msg]
>receiverSimpleAtoms (Atom v) = [Atom v]
>receiverSimpleAtoms (Encrypt k ms) = concat (map receiverSimpleAtoms ms)
>receiverSimpleAtoms (Sq ms) = concat (map receiverSimpleAtoms ms)
>receiverSimpleAtoms (Xor m m') = (receiverSimpleAtoms m) ++ (receiverSimpleAtoms m')
>receiverSimpleAtoms (Undec m v) = [Undec m v]
>receiverSimpleAtoms (Forwd _ m) = receiverSimpleAtoms m

>receiverSimpleAtoms (Sent m t) = receiverSimpleAtoms m++flatmap receiverSimpleAtoms t

Extract the simple atoms of a message as they are seen by the sender of a
mesage. This function is a mirror-function to the one above. The big difference
is, that Forwd-messages are completely removed, as the final set of atoms would
contain the same Forwd- and Undec-message.

>senderSimpleAtoms :: Msg -> [Msg]
>senderSimpleAtoms (Atom v) = [Atom v]
>senderSimpleAtoms (Encrypt k ms) = 
>  senderSimpleAtoms k ++ concat (map senderSimpleAtoms ms)
>senderSimpleAtoms (Sq ms) = concat (map senderSimpleAtoms ms)
>senderSimpleAtoms (Xor m m') = senderSimpleAtoms m ++ senderSimpleAtoms m'
>senderSimpleAtoms (Undec m _) = senderSimpleAtoms m
>senderSimpleAtoms (Forwd v m) = []
>senderSimpleAtoms (Apply f m) = senderSimpleAtoms m

>senderSimpleAtoms (Sent m t) = senderSimpleAtoms m++flatmap senderSimpleAtoms t

>extractMsgFromSent:: Msg -> Msg
>extractMsgFromSent (Sent m _) = m

>factsFromSentRep :: Annotated -> [Msg]
>factsFromSentRep = map (\ (_,x,_,_,_,_) -> x) . sentrep

>makeProcParameters :: Annotated -> String
>makeProcParameters an = commaConcat (makeProcParametersList an)

>makeProcParametersList :: Annotated -> [String]
>makeProcParametersList an = remdups [y | (_,_,z,_,_) <- procs an, y <- z]

The function creates the correct string for a deduction in the form
"(conclusion, {premiss1, premiss2})"

>makeSentDeductionString :: Annotated -> [Msg] -> [Msg] -> Msg -> String
>makeSentDeductionString an recv_premisses sent_premiss sent_conclusion =  
>   let
>      parameters = remdups (makeProcParametersList an)
>      simpleAtoms = remdups (flatmap receiverFields recv_premisses ++ 
>                               flatmap senderFields sent_premiss++
>                               senderFields sent_conclusion)
>      varsToGenerate = filter (not . isParam) simpleAtoms
>           where
>               isParam (Simple v) = v `elem` parameters
>               isParam (Subst v m) = False
>      conclusion_str = showSenderMsg an sent_conclusion
>      all_messages  = map receiverMsg recv_premisses ++ map senderMsg sent_premiss
>      premisses_str  = commaConcat (map (showMsg an) all_messages) 
>      generatorsStr = commaConcat (map gen varsToGenerate)
>           where
>               gen (Simple v) = v++" <- "++findtypeT an v
>               gen (Subst v m) = v++" <- "++typeSet an v m
>   in
>      "{( " ++ format 8 ", " [ conclusion_str, "{ "++premisses_str++" }"]++")"++
>      if generatorsStr == "" then "}"
>      else "\n"++spaces 10++"| "++generatorsStr++"}"

The following function generates the sent-deduction from the protocol
description and is the most important function of the whole system.

We discard the first message of the protocol if it comes from the environment
as it is not needed for internalised agents.

>makeSentRep:: VarTypeList -> ProtDesc' -> SentRep 
>makeSentRep fvts protdesc =
>   makeSentRep2 fvts protdesc [] [] []
>   where
>       (_, _, sender, _, _, _, _, _):protdesc' = protdesc

>makeSentRep2:: VarTypeList -> ProtDesc' -> [(Player,Msg)] -> [(Player,Msg)] -> 
>               [(Player,[Msg])] -> SentRep
>makeSentRep2 _ [] _ _ _ = []
>makeSentRep2 fvts (msg:msglist) lastreceived_list lastsent_list initiated_knowledge =
>  let 
>      (_, mn, sender, receiver, msgcontent, (test,_), _,_) = msg
>      atoms_in_msg			    = senderSimpleAtoms msgcontent
>      sender_received_messages	= [m | (pl,m) <- lastreceived_list, pl == sender]
>      sender_received_atoms	= concat (map receiverSimpleAtoms sender_received_messages)
>      sender_introduced_atoms	= concat [ia | (pl,ia) <- initiated_knowledge, pl == sender]
>      last_sent_player			= [m | (pl,m) <- lastsent_list, pl == sender]
>      next_initiated_player_knowledge	= remdups ([playerAtom sender,playerAtom receiver] 
>                                                  ++ sender_introduced_atoms 
>                                                  ++ sender_received_atoms 
>                                                  ++ atoms_in_msg)
>      next_sent_player			= (Sent msgcontent next_initiated_player_knowledge)
>      next_sent			    = (sender,next_sent_player) : 
>                                   filter (\ (p,m) -> p /= sender) lastsent_list
>      next_received_player		= [(receiver,msgcontent)]
>      next_received_list		= filter (\ (p,m) -> p /= sender) lastreceived_list ++
>                                    next_received_player
>      next_initiated_knowledge	= (sender, next_initiated_player_knowledge) : 
>                                   filter (\ (p,m) -> p /= sender) initiated_knowledge
>      test_str				    = if (test == []) then "" else (", " ++ test)
>      deduction			    = (sender,next_sent_player, sender_received_messages,
>                                    last_sent_player, test_str, mn)
>  in
>       if sender == Environment then 
>           makeSentRep2 fvts msglist lastreceived_list lastsent_list initiated_knowledge
>       else
>           deduction : makeSentRep2 fvts msglist next_received_list next_sent
>                                   next_initiated_knowledge 

*******************************************************************************
Deductions
*******************************************************************************

>makeSentDeductions :: Annotated -> Output
>makeSentDeductions an = 
>  let
>     proc_sets_internal =
>       map (\ (_,name,_,_,_) -> 
>              "deductions_"++name++"_with_honest") 
>           (procs an)
>     proc_sets_internal_dishonest = 
>       map (\ (_,name,_,_,_) -> 
>              "deductions_"++name++"_with_dishonest") 
>           (procs an)
>     proc_sets_external = map (\(_,name,_,_,_) -> "deductions_"++name++"_external") (procs an)
>  in
>     flatmap (makeDeductionsForProcess an) (procs  an)
>     ++
>     "  All_Internal_Deductions = " ++ 
>     makeUnion 4 (proc_sets_internal ++ proc_sets_internal_dishonest) ++ "\n"
>     ++
>     "  All_External_and_Internal_Deductions_ = "++
>     makeUnion 4 ("All_Internal_Deductions":proc_sets_external)
>     ++
>     "\n  All_Deductions = Union({Base_Deductions, All_External_and_Internal_Deductions})"

>makeDeductionsForProcess :: Annotated -> ProcessInfo -> Output
>makeDeductionsForProcess an (id, procname, args,_,generatedarguments) = 
>   let
>       allparameters            = makeProcParameters an
>   in
>       "  -- The paramaterised deductions\n\n"++
>       "  deductions_"++procname++"_0("++allparameters++") ="++
>       makeUnion 4
>           [makeSentDeductionString an recv_premisses sent_premiss conclusion |
>            (sender,conclusion,recv_premisses,sent_premiss,_,_) <- sentrep an,
>            sender == Agent id]++
>     "\n"
>     ++
>     "  -- Deductions for internalised "++procname++ " running with honest\n"++
>     "  -- agent\n"++
>     "  deductions_"++procname++"_with_honest =\n"++ 
>     "    Union({\n"++
>     "      deductions_"++procname++"_0("++allparameters++") |\n"++  
>     "        "++makeGenerators an args True++"\n"++
>     "      })\n\n"
>     ++
>     "  -- Deductions for internalised "++procname++" running with dishonest\n"++
>     "  -- agent.\n"++
>     "  deductions_"++procname++"_with_dishonest =\n"++ 
>     "    Union({\n"++
>     "      deductions_"++procname++"_0("++allparameters++") |\n"++ 
>     "        "++makeGenerators an args False++"\n"++
>     "      })\n\n"
>     ++
>     "  -- Deductions for external "++procname++" running with any agent\n"++
>     "  -- These are used to better approximate KnowableFact so as to reduce the\n"++
>     "  -- size of LearnableFact.\n"++
>     "  deductions_"++procname++"_external_0("++allparameters++") ="++
>     makeUnion 4
>       [makeSentDeductionString an recv_premisses 
>          (map extractMsgFromSent sent_premiss) (extractMsgFromSent conclusion) |
>            (sender,conclusion,recv_premisses,sent_premiss,_,_) <- sentrep an,
>            sender == Agent id]++
>     "\n"
>     ++
>     "  deductions_"++procname++"_external = \n"++
>     "    Union({\n"++
>     "      deductions_"++procname++"_external_0("++allparameters++") | \n"++
>     "        "++makeExternalGenerators an args procname ++"\n"++
>     "    })\n\n"

>makeGenerators :: Annotated -> [VarName] -> Bool -> Output
>makeGenerators an args runWithHonest = 
>  let
>    nonArgs = remdups [y | (_,_,z,_,_) <- procs an, y <- z] \\ args
>    generatedArgs = remdups [x | (_,_,_,_,xs) <- procs an, x <- xs]
>    status = if runWithHonest then InternalUnknown else InternalKnown
>    makeGenerator arg = arg ++ " <- " ++ if elem arg args then argset else typ
>       where
>           typ = findtype an arg
>           subtypes = findsubtypes an arg
>           argset = if arg == head args then "inter("++typ++",HONEST)"
>                    else if elem arg generatedArgs then "{" ++ commaConcat vars ++ "}"
>                    else typ
>           vars = allofSubtypeTypeStatus an typ subtypes status
>    makeRestrictions = if runWithHonest then s else "not("++s++")"
>       where s = andConcat ["honest("++arg++")" | arg <- intersection players nonArgs]
>    players = [pl | (pl,_,_,_,_) <- procs an]
>  in
>    commaConcat (map makeGenerator nonArgs++map makeGenerator args)++", "++ makeRestrictions

>makeExternalGenerators :: Annotated -> [VarName] -> String -> Output
>makeExternalGenerators an args procname = 
>   let
>    nonArgs = remdups [y | (_,_,z,_,_) <- procs an, y <- z] \\ args
>    generatedArgs = remdups [x | (_,_,_,_,xs) <- procs an, x <- xs]
>    externalAgents = remdups [head args | (SeqComp as) <- actualAgents an, (pn,args) <- as, 
>                                   pn==procname]
>    makeGenerator arg = arg ++ " <- " ++ if elem arg args then argset else nonargset
>       where
>           typ = findtype an arg
>           subtypes = findsubtypes an arg
>           argset = if arg == head args then "{"++commaConcat externalAgents++"}"
>                    else if elem arg generatedArgs then "{" ++ commaConcat vars ++ "}"
>                    else typ
>           nonargset = typ
>           vars = allofSubtypeTypeStatus an typ subtypes External
>  in
>    commaConcat (map makeGenerator nonArgs++map makeGenerator args)

>andConcat :: [String] -> String
>andConcat (x:[]) = x
>andConcat (x:xs) = x ++ " and " ++ andConcat xs
>andConcat [] = []

*******************************************************************************
Automagic System Generation
*******************************************************************************

The system is generated according to the following specification:
    if Secret(a,s,ids) then (agent a expects s to be shared only with ids)
        
        Two internalised agents are created
        One external agent is created
        For each type of variable that is generated by a process one value
        typ_P and if the type is the type of a secret variable typ_S.

    Any authentication specification (e.g. Agreement(a,b,vs)
        (if b completes a run with agent a then a thinks they were running with b and agree on vs)
        
        Two internalised agents are created (Alice and Bob)
        Two instances of b is created externally (Bob)
        
        For each authenticated variable (i.e. variable in vs) one value is 
        created; var_S. 
        For every authenticated type: if the type is also the type of a secret 
        variable then two variables typ_S and typ_P of status InternalUnknown 
        and InternalKnown respectively, otherwise just one variable typ_P 
        (InternalKnown and InternalUnknown).
        For every non-authenticated type: typ_P (InternalKnown and InternalUnknown)
        
    Any specification where GenerateSystemWithRepeatSection is specified:
        System is constructed as in above cases but the arguments to the 
        processes are changed as follows:
            if an argument var is generated by the external process and is 
            introduced during the repeated stage then the appropriate
            InternalUnknown variable is used (and the same InternalUnknown 
            variable is used for ALL external processes of this type).
            
            otherwise, arguments are generated as normal (i.e. external values
            are used for other generated variables, and different processes use
            different external values).
       
        Also, we treat every authenticated variable as secret; in other words
        the intersection between InternalUnknown and InternalKnown values
        is the empty set. This is to remove false attacks. 
        
        Lastly, external variables are only generated if they are introduced
        during the repeated section. This reduces the size of the types.
            
        Justification of this:
            By using the same values from InternalUnknown an unbounded number of
            sessions of the repeat section are simulated because as the values
            are InternalUnknown the internal agents will be able to perform the
            same non-repeat section. Therefore, they will also perform the
            repeat section using different values for the generated variables but
            the same values for all other variables (for example, tickets etc).
            This simulates an unbounded number of sessions where each one
            introduces a fresh value. By constructing two agents externally as
            described above this would check injective authentication.

>generateSystem :: Input -> Maybe_ Input
>generateSystem input = 
>   let
>       (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>           vts, iks, timestampinfo, inlines, actualAgents, withdraw, 
>	        unboundpar, generatesystem,
>           intruderId, intruderInitKnows, intruderProcs, 
>	        crackables, deductions, guessables, equivs, channels, newchannels, 
>           sessinfo) = input
>       -- We add all agents identities, and all (InternalUnknown) values to it
>       intruderInitKnows' = intruderInitKnows 
>           ++ [Atom y | (y,_,_,_) <- participants]
>           ++ [Atom y | (y,_,InternalKnown,_) <- vts']
>       -- We make every free variable have a subtype so that when declaring actual
>       -- variables we can ensure each variable is only used in one place (i.e. a's Nonce)
>       fvts' = map (\ (n,t,_) -> if t /= "TimeStamp" then (n,t,[t++"_"++n]) else (n,t,[])) fvts
>       --  Give explicit inverses for all new variables we create
>       iks' = remdups (concat (map process fiks))
>           where process (k1, k2) = 
>                   if isFn fnts k1 then [] 
>                   else if k1 == k2 then 
>                       [(ak, ak) | ak <- [v | (v,t,_,_) <- vts', t == findtype_ fvts k1]]
>                   else []
>       vts' = participants++generatedActualVars++vts
>       -- A participant is a server, agent, bank
>       -- Formally it is someone who appears as the first parameter of proc - e.g.
>       -- a is a participant because INITIATOR(a,s,na,nb)
>       generateParticipants = 
>           [t | (v,t,_,_) <- vts, v /= intruderId, elem t participantTypes] == []
>       participants = 
>           if generateParticipants then 
>               -- the user has not specified any participants, we shall do so
>               -- We generate two identities, both are of every participant type
>               [("Alice",t,Normal,[]) | t <- participantTypes]
>               ++[("Bob",findtype_ fvts externalResponderVar,Normal,[])]
>           else []
>       participantTypes = remdups [findtype_ fvts v | (v,_,_,_,_) <- procs]
>       agentOfType typ = 
>           if generateParticipants then "Bob" -- as it must be an actual agent being created 
>           else hd [v | (v,t,_,_) <- vts, t==typ]
>       -- All generated variables
>       generatedFreeVars = remdups (concat [vs | (_,_,_,_,vs) <- procs])
>       generatedFreeVarsTypes = remdups (map (findtype_ fvts) generatedFreeVars)
>       generatedActualVars = 
>           generatedActualVarsKnown ++ generatedActualVarsUnknown ++ generatedExternalVars
>       -- For every type of generated variable we create a variable that is known
>       -- to the intruder of that tupe.
>       generatedActualVarsKnown = concat [gen typ | typ <- generatedFreeVarsTypes]
>           where gen typ = [(typ++"_P", typ, InternalKnown, [])]
>       generatedActualVarsUnknown = 
>               (remdups . concat) (
>                   [genAuth arg | arg <- authenticatedVars]
>                    ++ [varForType typ | typ <- generatedFreeVarsTypes])
>           where 
>               secretTypes = map (findtype_ fvts) secretVars
>               genAuth arg = [(arg++"_S", typ, InternalUnknown, [typ++"_"++arg])]
>                  where typ = findtype_ fvts arg
>               varForType typ = 
>                   -- If generating a repeat section then we ensure the InternalUnknown variables are
>                   -- disjoin from the InternalKnown variables. Otherwise, since the
>                   -- non-repeat section typically involves generating a key it is possible
>                   -- that the intruder would know that key as it would also be InternalKnown.
>                   if typ `elem` secretTypes then 
>                       [(typ++"_S", typ, InternalUnknown, [])]
>                   else [(typ++"_P", typ, InternalUnknown, [])]
>       -- Actual variables with external type are generated such that each external
>       -- instance is initialised with variables no ther instance uses.
>       generatedExternalVars = concat [gen arg | arg <- argsToGenerateFor]
>           where 
>               argsToGenerateFor = remdups [arg | (id,_,_,_,gen) <- procs, 
>                   id == externalResponderVar, arg <- gen, isRepeatedVar arg]
>               gen arg = [(arg++"_E"++show i, findtype_ fvts arg, External, []) | i <- [1..externalAgentCount]]
>       authenticatedVars = (remdups . concat) [authArgs t | (_,_,t) <- auths]
>       secretVars = (remdups . concat) [secretVar s | s <- secrets]
>       -- The free var of the agent who will be the external responder
>       externalResponderVar = head ([b | Sec b _ _ <- secrets] ++ [b | (_,b,_) <- auths])
>       -- 1 agent for only secrecy checks, 2 for any authentication check.
>       externalAgentCount = if auths /= [] then 2 else 1
>       actualAgents'  = concat [gen id pname args generated | 
>            (id,pname,args,_,generated) <- procs, id == externalResponderVar]
>           where
>               gen id pname (f:args) generated = 
>                   -- We let all external agents have the same identity
>                   [SeqComp [(pname, (agentOfType (findtype_ fvts id)):map (compute i) args)] 
>                       | i <- [1..externalAgentCount]]
>                   where 
>                       compute i arg =
>                           if elem arg generated then 
>                               case generatesystem of 
>                                   GenerateRepeatSection _ _   ->
>                                       if isRepeatedVar arg then arg++"_E"++show i
>                                       else
>                                           let
>                                               (_,t,st) = hd (filter (\(v,_,_) -> v == arg) fvts')
>                                           in
>                                               hd (allofSubtypeTypeStatus_ vts' t st InternalUnknown)
>                                   GenerateStandard            -> arg++"_E"++show i
>                           else hd [v | (v,t,_,_) <- vts', t == findtype_ fvts arg]
>       -- True if generated variable v is introduced during the repeat section
>       isRepeatedVar v = 
>               case generatesystem of
>                   GenerateRepeatSection _ _   -> v `elem` (remdups (varsInRepeatedSection protdesc))
>                   _                           -> True
>           where
>               GenerateRepeatSection from to = generatesystem
>               varsInRepeatedSection [] = []
>               varsInRepeatedSection ((_,msgNo,_,_,msg,_):protdesc' @ protdesc) = 
>                   if msgNo == from then varsInRepeatedSection' protdesc
>                   else varsInRepeatedSection protdesc' \\ atoms msg
>               varsInRepeatedSection' [] = []
>               varsInRepeatedSection' ((_,msgNo,_,_,msg,_):protdesc') = 
>                   if msgNo == to then []
>                   else atoms msg++varsInRepeatedSection' protdesc'
>       -- We must perform basic type checking as the typechecking has not been done yet
>       (typecheck, typecheckerror) =
>           if length (remdups ([b | Sec b _ _ <- secrets] ++ [b | (_,b,_) <- auths])) > 1 then
>               (False, "GenerateSystem was supplied but the specifications are incompatible")
>           else if actualAgents /= [] then
>               (False, "GenerateSystem was supplied but actual agents were supplied")
>           else if [v | (v,_,st) <- fvts, st /= []] /= [] then
>               (False, "GenerateSystem was supplied but subtypes were supplied for free variables")
>           else if intruderId == "" then
>               (False, "Intruder name not given")
>           else if [t | (v,t,_,_) <- vts, v == intruderId] == [] then
>               (False, "Intruder type not given")
>           else if length [t | (v,t,_,_) <- vts, not (elem t participantTypes)] /= 0 then 
>               (False, "GenerateSystem was supplied but actual variables were supplied")
>           else if not generateParticipants && 
>                   sort participantTypes == sort [t | (_,t,_,_) <- vts] then
>               (False, "There is a role for which there are no actual variables that "++
>                       "can be given as the player for that type.")
>           else if generatesystem /= GenerateStandard && unknownMessages /= [] then
>               (False, "GenerateRepeatSection was specified but messages "++commaConcat unknownMessages++
>                       " are unknown.")
>           else (True, "")
>           where
>                   GenerateRepeatSection from to = generatesystem
>                   unknownMessages = [msgNo | msgNo <- [from, to], 
>                                               not (msgNo `elem` [msgNo | (_,msgNo,_,_,_,_) <- protdesc])]
>   in
>       if typecheck then 
>           Yes (fvts', fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>               vts', iks', timestampinfo, inlines, actualAgents', withdraw, 
>               unboundpar, generatesystem, intruderId,
>               intruderInitKnows', intruderProcs, crackables, deductions, guessables,
>               equivs, channels, newchannels, sessinfo)
>       else Error ("Error: "++typecheckerror)

