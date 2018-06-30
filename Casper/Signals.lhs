Functions used in Compile.lhs to construct data structures containing
information about signal events - e.g. identifying the messages
corresponding to the signal events.

>module Signals (
>  createSignals, createSecretSignals, getAllInfo, -- Annotate.lhs
>  createSignals_check                  -- Consistency.lhs
>  ) 

>where

>import Types
>import Messages
>import Atoms
>import Useful
>import Pprint
>import Annotated

------------------------- 
Functions used for gathering information of signal events for
Authentication Specifications.  
-------------------------

Function used to gather required information for each authentication
specification (for each element in 'auths'):

createSignals - returns a list of tuples, one for each authentication
spec. Each tuple contains 3 elements: 
	- Signal.Running info (MessageNr, AgentId);
	- Signal.Commit info (MessageNr, AgentId);
	- list of required variables for the auth. spec.

>createSignals :: ProtDesc -> Auths -> [AuthSignal]
>createSignals protdesc auths = 
>  map (createSignal protdesc) (stripAuthLabels auths)

>createSignal protdesc (a,b,at) = 
>  let	connectedlist = connected msgB protdesc
>	msgA = msgNr(head(lastlink (Agent a) (Agent b) [Agent b] 
>					(reverse(connectedlist))))
>	msgB = lastmsg (Agent b) protdesc
>  in  ((msgA,a),(msgB,b),(a:b:at))

>stripAuthLabels :: Auths -> [(AgentId,AgentId,[VarName])]
>stripAuthLabels = map (\ (a,b,v) -> (a,b,rmAuthLabel v))

>rmAuthLabel :: AuthType -> [VarName]
>rmAuthLabel v =
>	case v of
>	  NonInjectiveAgreement ls -> ls
>	  Agreement ls -> ls
>	  TimedNonInjectiveAgreement _ ls -> ls
>	  TimedAgreement _ ls -> ls
>	  _ -> []


----------------------------------------------------------------------
* createSignals_check is used in Consistency.lhs to verify whether the
authentication specifications in the input file make sense (i.e. there
exists running and commit events for requested specs).

>type ErrorMessage = String

>createSignals_check ::	ProtDesc -> Auths -> ErrorMessage
>createSignals_check protdesc = flatmap (createSignal_check protdesc)

>createSignal_check ::ProtDesc -> Auth -> ErrorMessage
>createSignal_check protdesc (a,b,auth) = 
>  let	connectedlist = connected msgB protdesc 
>	ls = lastlink (Agent a) (Agent b) [Agent b] 
>					(reverse(connectedlist))
>	errorMsg = if (length ls == 0) then
>		     "Error: " ++ 
>		      showAuth(a,b,auth) ++ 
>		      " is not correct.  " ++ a ++ " is not " ++
>		      "causally linked to " ++ b ++ ".\n\n"
>		   else ""   
>	msgB = lastmsg (Agent b) protdesc
>  in  errorMsg

>showAuth (a,b,auth) =
>  showAuthName auth++"("++a++","++b++showAuthArgs auth++")"

>showAuthName auth =
>   case auth of
>       Aliveness		                -> "Aliveness"
>       WeakAgreement		            -> "WeakAgreement"
>       NonInjectiveAgreement _	        -> "NonInjectiveAgreement"
>       Agreement _		                -> "Agreement"
>       TimedAliveness _		        -> "TimedAliveness"
>       TimedWeakAgreement _	        -> "TimedWeakAgreement"
>       TimedNonInjectiveAgreement _ _  -> "TimedNonInjectiveAgreement"
>       TimedAgreement _ _	            -> "TimedAgreement"

>showAuthArgs auth =
>   case auth of
>     NonInjectiveAgreement ls  -> ", [" ++ commaConcat ls ++ "]" ++ ")"
>     Agreement ls -> ", [" ++ commaConcat ls ++ "]" ++ ")"
>     TimedAliveness n -> ", " ++ show(n) ++ ")"
>     TimedWeakAgreement n -> ", " ++ show(n) ++ ")"
>     TimedNonInjectiveAgreement n ls -> ", " ++ show(n) ++ ", [" ++
>				         commaConcat ls ++ "]" ++ ")"
>     TimedAgreement n ls -> ", " ++ show(n) ++ ", [" ++
>				         commaConcat ls ++ "]" ++ ")"
>     _ -> ""

================================================================


lastlink A B cs msgs - returns the last message sent by A which is 
transitively before the last message participated by B.

>lastlink _ _ _ [] = []
>lastlink a b cs ((l,n,s,r,m,t):ms) = 
>			if not(member r cs) then lastlink a b cs ms
>			else if (s==a) then [(l,n,s,r,m,t)]
>			     else lastlink a b (add s cs) ms

>msgNr (_,nr,_,_,_,_) = nr

>add s [] = [s]
>add s ms = remdups(s:ms)

lastmsg a ms - returns the last message participated by a in ms.
(note:  error if a does not exist in ms)

>lastmsg a ms = last([n | (_,n,s,r,_,_)<-ms, s==a || r==a])

connected n ms - returns the list of elements in ms up to and
including message nr n.

>connected _ [] = []
>connected msgnr (m:ms) 
>	| msgnr == msgNr m	= [m]
>	| otherwise		= m:connected msgnr ms

dowalk takes argument of the form [(nr1,id1),(nr2,id2),info)] 
(e.g. createSignals), and returns a list of the form: [((nr,id),info)] 
(e.g. authwalked) as a result of merging the information together
for tuples which are equal.  For example,

dowalk [(("1","A"),("2","B"),[1]),(("1","A"),("1","B"),[2])] 

would give:  [(("1","A"),[1,2]),(("2","B"),[1]),(("1","B"),[2])]

>dowalk :: 
>    [((MsgNo,AgentId),(MsgNo,AgentId),[VarName])] ->
>    [((MsgNo,AgentId),[VarName])]

>dowalk [] = []
>dowalk (((n1,str1),(n2,str2),info):xs) =
>    addelem (n1,str1) (addelem (n2,str2) res) 
>        where res=dowalk xs
>              addelem tup []=[(tup,info)]
>              addelem tup ((otup,oinfo):elems) = 
>                 if tup==otup then (otup,remdups(info++oinfo)):elems
>                 else (otup,oinfo):addelem tup elems


The function collectAuthsInfo protdesc authwalked, returns type
[(N,ID,L)], one element for each element in authwalked, where N
corresponds to a message number, ID corresponds to an agent id and L
is the list of variables to be added as 'extra' component to the
message triple with number N.


>collectAuthsInfo protdesc = map (collectAuthsInfo1 protdesc)

>collectAuthsInfo1 protdesc ((n,a),ls) = 
>  let (sender,receiver,_) = head [(extract s,extract r,m) | 
>			(_,nr,s,r,m,_)<-protdesc, n==nr]
>  in (n,a,ls\\[sender,receiver])
>  where extract x = case x of
>               Agent a -> a
>               Environment -> ""

Above, the function extract also deals with environment messages,
since environment messages can also be signal events.

-----------------------------------------------------------------------
Functions used for gathering information of signal events for Secrecy
Specifications.
-----------------------------------------------------------------------

createSecretSignals returns a list of triples L, where for each
secrecy spec (id,sec,ls) there exists a tuple in L containing the
following elements:

	1) nr - message number corresponding to the signal event
	2) id
	3) sec
	4) ls

>-- type SecretSignal = (MsgNo, AgentId, Msg, [AgentId])
>createSecretSignals :: 
>    ProcessList -> ProtDesc -> Secrets -> [SecretSignal]

>createSecretSignals procs protdesc = map (createSecretSignal procs protdesc)

>createSecretSignal _ protdesc (Sec a m ls) =
>  (lastmsg (Agent a) protdesc, a, m, ls)
>createSecretSignal procs protdesc (StrongSec a m ls) =
>  let	init_A = head[c | (id,_,c,_,_) <- procs, id==a]
>	msgA = findSecretClaimMsg (Agent a) required_info init_A protdesc
>	required_info = remdups((atoms m)++ls)
>  in (msgA, a, m, ls)

The secret m in a secrecy spec. (A,m,ls) can take one of the following
forms:
		- Atom x, or
		- Apply f x, where x is of type [Msg].

In the case that m is of type Apply f x, it is assumed that the agent
A knows the value of the function name f.

For secrecy specs. of type Sec A sec ls, the signal event is linked to
the last message participated by agent A.

For secrecy specs. of type StrongSec A sec ls, the signal event is
linked to the first message where A knows all the values in sec and
ls.

>findSecretClaimMsg _ _ _ [] = ""
>findSecretClaimMsg a info knows ((_,n,s,r,m,_):ms) = 
>	if (a/=s && a/=r) then  findSecretClaimMsg a info knows ms
>	else if (a==r) then
>		let newknows = 
>			getId(s)++concat (map atoms (receiverAtomFields m))
>		    knows' = remdupsmerge knows newknows
>		in if and[member s knows' | s<-info] then n
>		   else findSecretClaimMsg a info knows' ms
>	     else 
>		    -- newknows handles case where a intro. fresh vars 
>		    -- in m and updates knows accordingly.
>		let newknows = atomsSend m
>		    knows' = remdupsmerge knows newknows
>		in
>		  if and[member s knows' | s<-info] then n
>		  else findSecretClaimMsg a info knows' ms
>	where
>		getId(Agent a) = [a]
>		getId(Environment) = []

>receiverAtomFields :: Msg -> [Msg]
>receiverAtomFields (Atom v) = [Atom v]
>receiverAtomFields (Encrypt _ ms) = 
>  sortremdupsconcat (map receiverAtomFields ms)
>receiverAtomFields (Sq ms) = sortremdupsconcat (map receiverAtomFields ms)
>receiverAtomFields (Xor m m') = 
>  remdupsmerge (receiverAtomFields m) (receiverAtomFields m')
>receiverAtomFields (Undec _ v) = [Atom v]
>receiverAtomFields (Forwd _ m) = receiverAtomFields m
>receiverAtomFields (Apply _ _) = []


>combineInfo :: [ExtraInfo] -> [ExtraInfo]
>combineInfo = foldr addelem []

>addelem :: ExtraInfo -> [ExtraInfo] -> [ExtraInfo]
>addelem tup []=[tup]
>addelem (nr,id,ls) ((nr2,id2,ls2):elems) = 
>                 if nr==nr2 && id==id2 then (nr2,id2,remdups(ls++ls2)):elems
>                 else (nr2,id2,ls2):addelem (nr,id,ls) elems

>mergeInfo :: [ExtraInfo] -> [ExtraInfo] -> [ExtraInfo]
>mergeInfo xs ms = foldl (flip addelem) ms xs

>collectSecretInfo protdesc as = map (collectSecretInfo1 protdesc) as

>collectSecretInfo1 protdesc (n,a,ls) = 
>  let  (sender,receiver,_) = head [(extract s,extract r,m) | 
>                       (_,nr,s,r,m,_)<-protdesc, n==nr]
>  in (n,a,ls\\[sender,receiver])
>  where extract x = case x of
>               Agent a -> a
>               Environment -> ""

======================================================================

Each element of extra info is of the form (n, a, ls).  It represents that
agent a needs to include the extras ls in message number n.


>getAllInfo :: ProtDesc -> [AuthSignal] -> [SecretSignal] -> [ExtraInfo]
>getAllInfo protdesc authsignals secretsignals =
>  let authsinfo = collectAuthsInfo protdesc (dowalk authsignals)
>      secretsignals' = [(nr,id,remdups(atoms(sec)++ls)) | 
>		                   (nr,id,sec,ls) <- secretsignals]
>      secretinfo = collectSecretInfo protdesc (combineInfo secretsignals')
>      allinfo2 = mergeInfo authsinfo secretinfo
>  in [(nr,id,ls) | (nr,id,ls) <- allinfo2, ls/=[]]
