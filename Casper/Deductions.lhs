>module Deductions (
>    makeOrdering
>  )

>where

TODO: CLEANUP AND REMOVE DEAD CODE HERE

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import Annotated

Generating the Deduction List

For each internal process with identity I, we want to construct a list
of deductions with the following structure:

	[(MsgNo, AgentId, [Msg], [(Player,[Msg])])]

where:	Element 1 is Msg Number created by this deduction;
	Element 2 is the process identity Id;
	Element 3 is the list of msgs being deduced.
	Element 4 is the list of msgs upon which this deduction is
	  dependent - this list consists of pairs (S,Ms) where S is
	  the sender of the message with components Ms.  Ms only ever
	  represents 1 message - we convert the message into a list to
	  handle the Sq. structure.

-------------------------------------------------------------------
Overall Deduction Function

>makeDeduction1 generationNrs revProtdesc p =
>  let
>	thisRprotdesc = 
>		[(n,s,r,m) | (_,n,s,r,m,_,_,_) <- revProtdesc,
>		  Agent p == s || Agent p == r]
>  in
>	makeDeductionList p generationNrs thisRprotdesc


-------------------------------------------------------------------

makeDeductionList - returns the list of deductions for one internal
process, represented by the type: 

	[(MsgNo, AgentId, [Msg], [(Player,[Msg])])]

and handles:

1. The case of Sq. structures (splits into a list of the sub
   messages) - this is why the 3rd element and the second component of 
   the 4th element is a list representing ONE message M (i.e. type:
  [Msg]), rather than simply M itself (i.e. type: Msg).

2. removes duplicates;

3. removes elements in the generated message list which are already
   present in the required list - this can otherwise cause problems
   with the synchronisations between the intruder components.

>makeDeductionList :: 
>	AgentId ->
>	[MsgNo] ->	-- generationNrs
>	[(MsgNo, Player, Player, Msg)] ->
>	[(MsgNo, AgentId, [Msg], [(Player,[Msg])])]

>makeDeductionList _ _ [] = []
>makeDeductionList p generationNrs ((n,s,_,m):ls) =
>  if (Agent p==s && not(member n generationNrs)) then
>    let  reqMsgs = [(s,rmSq(msg)) | (_,s,_,msg) <- ls]
>	  deds = remdups(rmSq(m))
>	  mergeReqMsgs = concat[msgs | (_,msgs) <- reqMsgs]
>	  deductions = [m | m <- deds, not(member m mergeReqMsgs)]
>    in
>		(n,p,deductions,reqMsgs):
>			makeDeductionList p generationNrs ls
>  else 
>    makeDeductionList p generationNrs ls
>  where
>	rmSq (Sq ls) = ls
>	rmSq m = [m]


* reqMsgs - represents the list of messages from which m is deduced.
This is simply all messages involving p occuring before m in protdesc
(i.e. ls, since ls was commuted using the reverse(protdesc) and only
with messages sent or received by p).  We store this as pairs (s,ms)
rather than simply a list of msgs, since we need to be able to
determine (from this data structure) whether p is the sender or
receiver, later when we construct the corresponding CSP string for
each deduction set (i.e. in the function printDiDeduction).

* In both reqMsgs and deds, we apply the function rmSq to remove the
top layer of the Sq. structure (required in our CSP model of the
intruder).

* mergeReqMsgs is used to ensure point 3 above (in deductions).

For a given internal process P and message M, we need to construct a
deduction triple iff: 
	  1.  P is the Sender of M, AND
	  2.  P does not introduce any fresh values in M (since this
	  will be dealt with in the Generations sets).

======================================================================
Generations for Internal Processes (Data Independence)

---------------------------------------------------------------------
makeDiGenerations - returns the list of all generations required for
the internal processes and is represented by the type: 

	[([MsgNo], AgentId, [(Player,[Msg])],[Msg])]

>makeDiGenerations ::
>   [(MsgNo,(AgentId,[VarName]),(AgentId,[VarName]))] ->  -- accumList
>   ProtDesc' -> [VarName] ->	-- protdesc, intruderProcsId
>   [([MsgNo], AgentId, [(Player,[Msg])],[Msg])]	
>				-- resulting list of diGenerations

>makeDiGenerations accumList protdesc  =
>  flatmap (makeDiGeneration accumList protdesc)

>makeDiGeneration accumList protdesc p =
>  let
>	thisprotdesc = 
>		[(n,s,r,m) | (_,n,s,r,m,_,_,_) <- protdesc,
>		  Agent p == s || Agent p == r]
>  in
>	makeGenerationList p accumList [] thisprotdesc


-------------------------------------------------------------------
makeGenerationList - returns the list of generations for one internal
process p.

For each internal process P, we construct a list of generations of the 
form:  [(Nrs, P, ReqMsgs, GenMsgs)], where

* Nrs - is a list of message numbers which belong to one "generation
group" and will be generated in one Generation Set.

* ReqMsgs - is the list of messages involving P and preceding those
messages being generated (i.e. those in GenMsgs).  This list actually
consists of tuples (Id, msg) since we need to know the sender of each
of these "required" messages when printing them out (in order to
handle % in printDiGenerations).

* GenMsgs - is the list of messages which will be generated in this
Generation Set.  Here, we don't need to store the Sender of each
message, since by definition it will be P in each case.

>makeGenerationList ::
>   AgentId ->				-- internal process id
>   [(MsgNo,(AgentId,[VarName]),(AgentId,[VarName]))] ->  -- accumList
>   [(Player,Msg)] ->			-- accumulated msgs for reqs.
>   [(MsgNo, Player, Player, Msg)] ->	-- thisprotdesc
>   [([MsgNo], AgentId, [(Player,[Msg])], [Msg])]
>   -- resulting list of diGenerations for one internal process

For each internal process P, we perform the following steps to
construct the corresponding list of generations:

1. Filter out all messages not involving P from protdesc (and simplify 
the structure to (MsgNo,Player,Player,Msg)) = thisprotdesc.

2. Call makeGenerationList P accumList [] thisprotdesc to construct
the list of generations. [] is the initialisation of the set
containing all preceding messages to thisprotdesc involving P.

For a given internal process P, we perform the following steps to
construct 1 Generation (1 loop of makeGenerationList):

1.  Take the first element of thisprotdesc (n,s,r,m), where we will
call the remaining list ls;

2.  If P is the sender (P==s) and m introduces fresh values of DI
type, then:
	
	2.2. gather all subsequent (sequential) messages from ls,
	     where P is the sender, to construct the Generation Group:
	     This is done by stepping through ls and collecting all
	     elements until P is not the Sender.

	     This will form 1 Generation.

	2.3. (generatedMsgs) From 2.2. construct the list of generated
	     msgs of type [Msgs] (removing all message components
	     which are already present in Reqs).

	2.4. (genNrs) From 2.2. construct the list of generated msg
	     numbers.

	2.3. reqs is the list of all messages preceding (n,s,r,m) and
	     therefore all the messages required for this generation.

	2.4. Construct the Generation tuple:

		(gensNrs, P, reqs, generatedMsgs)

3.  Update the parameters for the next loop to construct the next
    generation.


>makeGenerationList _ _ _ [] = []
>makeGenerationList p accumList reqs ((n,s,r,m):ls) =
>  if (Agent p==s && (new (n,p) accumList)) then
>    let  reqMsgs = [(s,rmSq(m)) | (s,m) <- reqs]
>	  gens = (n,s,r,m):gatherGenerationGroup p ls
>	  gensMsgs = [m | (_,_,_,m) <- gens]
>	  gensNrs = [n | (n,_,_,_) <- gens]
>	  gensM = remdups(concat(map rmSq gensMsgs)) 
>	  mergeReqMsgs = concat[msgs | (_,msgs) <- reqMsgs]
>	  generatedMsgs = [m | m <- gensM, not(member m mergeReqMsgs)]
>	  rest = [(n,s,r,m) | (n,s,r,m) <- ls, not(member n gensNrs)]
>	  reqs' = reqs ++ [(s,m) | (_,s,_,m) <- gens]
>    in
>	   (gensNrs, p, reqMsgs, generatedMsgs):
>			makeGenerationList p accumList reqs' rest
>  else 
>	makeGenerationList p accumList (reqs++[(s,m)]) ls
>  where
>	new _ [] = False
>	new (nr,x) ((n1,(s1,sls),_):accumList) =
>		(nr==n1 && x==s1 && sls/=[]) || new (nr,x) accumList
>	rmSq (Sq ls) = ls
>	rmSq m = [m]

>gatherGenerationGroup _ [] = []
>gatherGenerationGroup p ((n,s,r,m):ls) = 
>	if (Agent p==s) then (n,s,r,m):gatherGenerationGroup p ls
>	else []


For a given internal process P and message M, we need to construct a
generation triple iff: 
	  1.  P is the Sender of M, AND
	  2.  P introduces one or more fresh values in M.

===================================================================

Functions used in Intruder.lhs to generate the CSP code for the
deductions and generation sets.

----------------------------------------------------------------------
printDiDeductions - returns a string representing the CSP for the
extra deductions of the internal processes (used only for di input
files).

>printDiDeductions ::
>	VarTypeList -> FnTypeList ->		     -- fvts; fnts
>	DataTypeDefs ->				     -- dtdefs
>	[TypeName] ->				     -- dit
>	[(MsgNo,AgentId,[Msg],[(Player,[Msg])])] ->  -- diDeductions
>	Output


>printDiDeductions _ _ _ _ [] = ""
>printDiDeductions fvts fnts dtdefs dit intDeductions =
>  let	range = [nr | (nr,_,_,_) <- intDeductions]
>  in
>    printDeductions1 fvts fnts dtdefs dit intDeductions ++
>    "Agent_Deductions = " ++ 
>	     (frontLabelUnion "Proc_Deduction" 15 range) ++ "\n\n"


>printDeductions1 _ _ _ _ [] = ""
>printDeductions1 fvts fnts dtdefs dit ((nr,p,deds,reqs):intDeds) =
>  let 
>--       fvts' = [(v,"All_" ++ t) | (v,t) <- fvts, member t dit]
>--	        ++ [(v,t) | (v,t) <- fvts, not(member t dit)]
>	msg_deds = map (showMsg fvts fnts.senderMsg) deds
>	msgReqsSend = remdups(concat [msgs | (s,msgs) <- reqs,
>						s==Agent p])
>	msgReqsRec = remdups(concat [msgs | (s,msgs) <- reqs,
>						s/=Agent p])
>	showReqsSend = map (showMsg fvts fnts.senderMsg) msgReqsSend
>	showReqsRec = map (showMsg fvts fnts.receiverMsg) msgReqsRec
>       msgs_reqs = remdups(showReqsSend ++ showReqsRec)
>	rangeInfo_deds = concat(map senderFields deds)
>	rangeInfo_reqsSend = concat(map senderFields msgReqsSend)
>	rangeInfo_reqsRec = concat(map receiver2Fields msgReqsRec)
>	rangeInfo = remdups(rangeInfo_deds ++ rangeInfo_reqsSend 
>				++ rangeInfo_reqsRec)

>  in
>	("Proc_Deduction" ++ nr ++ " =\n" ++
>	 spaces 5 ++ "{(Msg"++ nr ++ ",\n" ++
>	 spaces 5 ++ "{" ++ format 5 ", " msg_deds ++ "},\n" ++
>	 spaces 5 ++ "{" ++ 
>	 format 5 ", " msgs_reqs ++ "}) | \n" ++ spaces 7 ++
>	 format 10 ", " (makeVarGens fvts fnts dtdefs rangeInfo) ++
>	 "}\n\n") ++
>	printDeductions1 fvts fnts dtdefs dit intDeds

* Above, for constructing the corresponding CSP strings, we
distinguish between required messages sent by p (msgReqsSend) and
those received by p (msgReqsRec).  We need this distinction for
correctly handling the case of %.

* We use senderMsg and receiverMsg to handle the case of % correctly.

----------------------------------------------------------------------
printDiGenerations - returns a string representing the CSP for the
generation sets of the internal processes (used only for di input
files).

>printDiGenerations ::
>   VarTypeList -> FnTypeList ->			 -- fvts; fnts
>   DataTypeDefs ->					 -- dtdefs
>   [(MsgNo,(AgentId,[VarName]),(AgentId,[VarName]))] -> -- accumList
>   [([MsgNo],AgentId,[(Player,[Msg])],[Msg])] ->	 -- Generations
>   Output

>printDiGenerations _ _ _ _ [] = 
>  "Error in makeGenerations Set:  Should not be called with empty list.\n"

>printDiGenerations fvts fnts dtdefs accumList inferenceList =
>  let 
>	ordering = makeOrdering fvts accumList inferenceList
>	-- range = [opConcat "_" nrs | (nrs,_,_,_) <- inferenceList]
>  in flatmap (printGenerations1 fvts fnts dtdefs ordering) inferenceList
>     -- "  Generations = "++(frontLabelUnion "Generation_" 15 range)++"\n\n"

>printGenerations1 fvts fnts dtdefs ordering (nrs,p,reqs,gens) =
>  let 
>--       fvts' = [(v,"All_" ++ t) | (v,t) <- fvts, member t dit]
>--	        ++ [(v,t) | (v,t) <- fvts, not(member t dit)]
>	genMs = map (showMsg fvts fnts.senderMsg) gens
>	-- s in(s,msgs) is the sender of the msg with component msgs.
>	msgReqsSend = remdups(concat [msgs | (s,msgs) <- reqs,
>						s==Agent p])
>	msgReqsRec = remdups(concat [msgs | (s,msgs) <- reqs,
>						s/=Agent p])
>	showReqsSend = map (showMsg fvts fnts.senderMsg) msgReqsSend
>	showReqsRec = map (showMsg fvts fnts.receiverMsg) msgReqsRec
>       reqMs = remdups(showReqsSend ++ showReqsRec)
>	rangeInfo_deds = concat(map senderFields gens)
>	rangeInfo_reqsSend = concat(map senderFields msgReqsSend)
>	rangeInfo_reqsRec = concat(map receiver2Fields msgReqsRec)
>	rangeInfo = remdups(rangeInfo_deds ++ rangeInfo_reqsSend 
>				++ rangeInfo_reqsRec)
>	ls = getOrder nrs ordering
>	-- ls is a list of lists, one for each DI type which has fresh
>	-- values introduced in this msg nr (e.g. [["na","nb"],["kab"]]). 
>	freshVars = concat(ls)
>	freshRange = [v ++ " <- F" ++ findtype an v | v <- freshVars]
>	otherRange = rangeInfo\\(varFields2(freshVars))
>  in
>	("  Generation_" ++ opConcat "_" nrs ++ " =\n" ++
>	 spaces 4 ++ "{(" ++ 
>	 (if (ls /= []) then "("++commaConcat(makeAllSeqs ls)++")"
>	  else error "Error in ordering parameter.\n\n\n") ++",\n"++
>        spaces 6++ "{ " ++ format 8 ", " reqMs ++ " },\n" ++ 
>	 spaces 6 ++ "{ " ++ format 8 ", " genMs ++ " }" ++ ") |\n" ++ 
>        spaces 8 ++
>	 format 8 ", " (makeVarGens fvts fnts dtdefs otherRange)++",\n"++ 
>        spaces 8 ++format 8 ", " freshRange++ "}\n\n") 
>  where
>	 getOrder _ [] = []
>	 getOrder nrs ((nrs',ms):ls) = 
>		  if (equalityLists nrs nrs') then
>		        [vars | (_,vars) <- ms]
>		  else getOrder nrs ls
>	 makeAllSeqs [] = []
>	 makeAllSeqs (ls:xs) =
>	    ("<" ++ commaConcat ls ++ ">"):makeAllSeqs xs

----------------------------------------------------------------------
* "ordering" is used to store the ordering of fresh values introduced
by internal agents only.  This ordering is used in the spypick events
and the generation sets.  For example:

        [(["1","2"],[("Nonce",["na","nb"]),("Key",["kab"])])]

means that for the generation G for messages 1 and 2, the ordering of
the fresh values introduced in G and the corresponding spypick events
is:
        spypick.(<na,nb>,<kab>)

where the Nonce Manager will synchronise with this and provide the two
nonces and the Key Manager will provide the fresh key.

-----------------------------------------------------------------------
General functions used locally in this file.

>frontLabelUnion :: String -> Int -> [String] -> String

>frontLabelUnion _ _ [] = "{}"
>frontLabelUnion label _ [l] = label ++ l
>frontLabelUnion label n ls = 
>	"Union({" ++ commaNlConcat n (labelFront label ls) ++"})"

------------------------------------------------------------------
makeOrdering
------------------------------------------------------------------

>makeOrdering ::
>   VarTypeList ->				  -- fvts
>   FreshVarList ->				  -- accumList
>   [([MsgNo],AgentId,[(Player,[Msg])],[Msg])] -> -- Generations
>   [([MsgNo], [(TypeName, [VarName])])]

>makeOrdering _ _ [] = []
>makeOrdering an accumList generations =
>   let	freshList = [(nrs,getFresh nrs accumList) | 
>				(nrs,_,_,_) <- generations]
>	typeOrder = remdups(concat[map (findtype an) sl | 
>				       (_,sl) <- freshList])
>   in
>	makeAllOrderings fvts typeOrder freshList
>   where
>	-- list all the fresh vars introduced in the msgs in nrs.
>	getFresh _ [] = []
>	getFresh nrs ((n,(_,sl),_):accumList) =
>		if member n nrs then sl ++ getFresh nrs accumList
>		else getFresh nrs accumList
>	makeAllOrderings _ _ [] = []
>	makeAllOrderings fvts typeOrder ((nrs,sl):sAccumList) =
>		(nrs,makeOneOrdering fvts sl typeOrder):
>		  makeAllOrderings fvts typeOrder sAccumList
>	makeOneOrdering _ _ [] = []
>	makeOneOrdering fvts sl (t:types) =
>	   (t,getElems fvts t sl):makeOneOrdering fvts sl types
>	getElems _ _ [] = []
>	getElems fvts t (s:sl) =
>	  let	istype = (findtype an s)==t
>	  in
>		if istype 
>		then 
>		     s:getElems fvts t sl
>		else 
>		     getElems fvts t sl
