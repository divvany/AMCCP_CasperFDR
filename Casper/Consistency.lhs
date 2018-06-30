Perform various consistency checks, particularly concerning agents' abilities
to send and receive messages.

>module Consistency(consistency, consistencypd) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import Signals

>type Warning = String

>consistency :: Input -> (String, String)
>consistency 
>  (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs, actvts, _, 
>   _, _, actualAgents, _, unboundpar, generateSystem, _, _, _, _, _, _, _, _, _, _) =
>  let vts = [(v,t,st) | (v,t,_,st) <- actvts]
>      (es, warnings) = 
>         consistencypd (fvts, fnts, fiks, dtdefs, procs, protdesc, 
>                        secrets, auths)
>      actualAgentAtoms = 
>        [aa | Star aa <- actualAgents] ++ 
>        concat [aas | SeqComp aas <- actualAgents]
>      error_authSignals = createSignals_check protdesc auths
>      error_unboundparNoenvmessage = unboundpar_check (head protdesc) secrets unboundpar
>-- throw an error if running a secrecy check in the unbounded
>-- parallel model with no initial message from environment
>--      errors = es ++ error_authSignals
>      errors = es ++ error_authSignals++ error_unboundparNoenvmessage
>      all_warnings = warnings
>  in (checkActualSystem fvts procs vts actualAgentAtoms ++ errors, 
>							  all_warnings)

>unboundpar_check (_,_,p1,_,_,_) secrets unboundpar = 
>  if (not (null secrets)) && unboundpar && (not (show p1 == "Environment")) then err else ""
>    where err = "When testing secret specifications in the unbounded parallel model, the first message of the protocol must be sent by the environment."

* createSignals_check - ensures that for each authentication
specification, there is a Running event which transitively precedes
the corresponding Commit event.  (Defined in Signals.lhs.)

>consistencypd :: Inputpd -> (String, String)
>consistencypd (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths) =
>  let ews = 
>        map (checkProcessDef fvts fnts fiks dtdefs secrets auths protdesc)
>            procs
>  in (flatmap fst ews, flatmap snd ews)

=========================================================================

--  >maybeString :: Bool -> String -> String
--  >maybeString True st = st
--  >maybeString False _ = ""

=========================================================================

Check that each agent in turn is able to run the protocol--i.e. that they
possess all the relevant information at each step.

>checkProcessDef :: 
>  VarTypeList -> FnTypeList -> InverseKeyList -> DataTypeDefs -> 
>  Secrets -> Auths -> ProtDesc -> 
>  ProcessInfo -> (Warning, Warning)

warnings in first returned value are fatal; warnings in second are just
warnings

>checkProcessDef fvts fnts fiks dtdefs secrets auths protdesc
>        (id, _, args, knows, generates) = 
>  let -- add datatype constructors to knows and args
>      knows' = knows++[Atom cons | (_,pats,_) <- dtdefs, (cons, _:_) <- pats]
>      args' = args++[cons | (_,pats,_) <- dtdefs, (cons, []) <- pats]
>			++generates
>      (errors, warnings, finalargs) = 
>        checkProcessNextStep fvts fnts fiks id "" "" 
>                             args' knows' auths protdesc
>      secrets' = -- secrets for this agent
>        [(a,s,bs) | Sec a s bs <- secrets, a==id] ++ 
>        [(a,s,bs) | StrongSec a s bs <- secrets, a==id]
>      -- ok m = canSenderProduce fvts fnts finalargs knows' m
>      --ok (Atom v) = member v finalargs
>      --ok (Apply f m) = canApplyFn fvts fnts finalargs knows' (Apply f m)
>      --ok _ = False
>  in
> (errors ++
>  concat ["Secret "++showMsg_ fvts fnts s++" never known by "++a++"\n" | 
>             (a, s, _) <- secrets', 
>             not (canSenderProduce fvts fnts finalargs knows' s)] ++
>  concat ["In secret specification for "++showMsg_ fvts fnts s++
>          " of agent "++a++", agent "++b++" not known\n" | 
>                 --  ++show finalargs++"\n"
>             (a, s, bs) <- secrets', b <- bs, not (member b finalargs)],
>  warnings)

Generate list of errors and warnings relating to this agent; also calculate 
final knowledge in args.

>checkProcessNextStep :: 
>  VarTypeList -> FnTypeList -> InverseKeyList ->      -- fvts fnts fiks 
>    AgentId -> Warning -> Warning ->                  -- id errs ws
>    [Argument] -> [Msg] -> Auths -> ProtDesc ->       -- args knows auths ms
>    (Warning, Warning, [Argument])

>checkProcessNextStep _ _ _ _ errs ws args _ _ [] = 
>  (errs, ws, args)
>checkProcessNextStep fvts fnts fiks id errs ws args knows auths (m:ms) =
>  let lastOut = and [s /= id | (_,_,Agent s,Agent _,_,_) <- ms]
>      lastMsg = and [s /= Agent id && r /= Agent id | (_,_,s,r,_,_) <- ms]
>      (errs', ws', args') = 
>        checkProcessStep fvts fnts fiks id args knows auths lastOut lastMsg m 
>  in checkProcessNextStep fvts fnts fiks id (errs++errs') (ws++ws') 
>                        args' knows auths ms

>checkProcessStep fvts fnts fiks id args knows auths lastout lastmsg
>                 (assigns, no, sender, receiver, msg,  _) 
>  | Agent id == sender  
>    = checkProcessSenderStep fvts fnts  id args knows auths  
>                             assigns no receiver msg lastout lastmsg
>  | Agent id == receiver
>    = checkProcessReceiverStep fvts fnts fiks id args knows auths  
>                             no sender msg lastmsg
>  | otherwise  
>    = ("", 
>       -- "Missing message "++show no++" for "++id++" sender = "++
>       -- show sender++" receiver = "++show receiver++"\n", 
>       "",
>       args)

Check next bit of process definition if agent sends this message

>checkProcessSenderStep fvts fnts id args knows auths 
>                       assigns no receiver msg lastout lastmsg =
>  let assvars = map fst assigns
>      args' = args ++ assvars
>      Agent rec = receiver
>      repeatassvars = 
>        [v | (n,v) <- zip [1..] assvars, 
>             member v args || member v (drop n assvars)]
>      assignerrs =
>        concat ["Attempt to redefine variable "++v++
>                " within assignment by "++id++"\n" | 
>                  v <- repeatassvars]
>      badfields1 = 
>        if receiver/=Environment && not (member rec args') then [Atom rec] 
>        else []
>      badfields = badfields1 ++
>                  [af | af <- senderAtomFns msg,
>                        not (canSenderProduce fvts fnts args' knows af),
>                        not (isTimeStamp af)]
>      isTimeStamp (Atom a) = findtype_ fvts a == "TimeStamp"
>      isTimeStamp (Apply _ _) = False
>      errs =
>        if badfields /= []  
>        then "Unknown field(s) in message "++no++" for sender: "++
>             commaConcat (map (showSenderMsg_ fvts fnts) badfields)++"\n"
>        else ""
>      runningws =
>        if lastout
>        then
>         ["In authentication specification, agent "++id++
>          " does not know "++d++" by message "++no++"\n" |
>             d <- concat [b:authArgs at | (a,b,at) <- auths, a == id],
>             not (member d args')]
>        else []
>      commitws = 
>        if lastmsg
>        then
>          ["In authentication specification, agent "++id++
>           " does not know "++d++" by message "++no++"\n" |
>              d <- concat [b:authArgs at | (b,a,at) <- auths, a == id],
>              not (member d args')]
>        else []
>  in (concat runningws ++ assignerrs ++ errs ++ concat commitws,
>      -- "Sender step " ++ show no ++ " for " ++ id++"\n", 
>      "",
>      args')

Check next bit of process definition if agent receives this message

>checkProcessReceiverStep fvts fnts fiks id args knows auths 
>       no sender msg lastmsg =
> let cpts = components1 (receiverMsg msg)
>     percentvars = receiverPerCents msg 
>     repeatedpercentvars = reps percentvars
>     newargs = [a | Atom a <- cpts]
>     args' = case sender of
>               Environment -> remdups (args ++ newargs)
>               Agent s     -> remdups (s : args ++ newargs)
>     encs = [Encrypt k m | Encrypt k m <- cpts]
>     xors = [Xor m m' | Xor m m' <- cpts]
>     (ks,xorerrs,args'') = 
>       canDecrypt fvts fnts fiks args' knows encs xors
>     recFnApps1 = -- function applications not immediately in rec's knowledge
>       [(f,m) | (f,m) <- receiverfnApps msg, 
>                 not (member (Apply f m) knows)]
>     badfnapps1 = 
>       [(f,m) | (f,m) <- recFnApps1, not (knowsFn fnts knows f)]
>     recFnAppsBadArgs = 
>       [(f,m, [a | a <- receiverAtomFns m, 
>                   not (canReceiverProduceAtom fvts fnts args'' knows a)]) |
>            (f,m) <- recFnApps1]
> in ((if lastmsg
>      then
>        concat 
>         ["In authentication specification, agent "++id++
>          " does not know "++d++" after message "++no++"\n" |
>             d <- concat [b:authArgs at | (b,a,at) <- auths, a == id],
>             not (member d args'')]
>      else "")
>     ++ 
>     concat ["Key "++inverse1 fiks k++" not in agent "++
>             id++"'s state at message "++no++".\n" | 
>               Atom k <- ks] ++
>     concat ["Key "++
>             showFn fnts (showMsg_ fvts fnts) (Apply (inverse1 fiks f) m)++
>             " not in agent "++id++"'s state at message "++no++".\n" |  
>                  Apply f m <- ks] ++
>     concat ["Agent "++id++" cannot decrypt message "++
>             showMsg_ fvts fnts m++"\n" |
>                m <- xorerrs] ++
>     concat ["Receiver does not know function "++f++" in message "++no++"\n" |
>                (f,_) <- badfnapps1] ++
>     concat ["Receiver cannot perform function application: \n"++
>             showFn fnts (showMsg_ fvts fnts) (Apply f m)++
>           " in message "++no++" because he cannot produce field(s):\n" ++
>           commaConcat (map (showMsg_ fvts fnts) args) ++"\n" | 
>                (f,m,args) <- recFnAppsBadArgs, args /= []],
>     -- warnings:
>     concat 
>       ["Warning: repeated variable on right hand side of % construct for "++
>        id++": "++v++"\n" | 
>           v <- percentvars, member v args]
>     ++ 
>     concat 
>       ["Warning: repeated variable on right hand side of % construct for "++
>        id++": "++v++"\n" | 
>           v <- repeatedpercentvars],
>     -- new knowledge
>     args'')

Repeated elements of argument

>reps [] = []
>reps (x:xs) = if member x xs then x:reps(remove xs x) else reps xs

Check whether agent can decrypt all encrypted messages in encs, or Vernam
encrypted messages in xors, returning list of keys that are (erroneously)
unknown, list of Vernam encryptions that can't be undone, and final knowledge

>canDecrypt :: 
>  VarTypeList -> FnTypeList -> InverseKeyList -> [Argument] -> 
>  [Msg] -> [Msg] -> [Msg] ->
>  ([Msg], [Msg], [Argument])

>-- Firstly, case where all decryptions have been done
>canDecrypt _ _ _ args _ [] [] = ([],[],args)

>canDecrypt fvts fnts fiks args knows encs xors = 
>  let allargs = args -- ++ holds -- ++ knows
>      unEncs = -- encryptions that can be undone
>        [Encrypt (Atom k) ms | Encrypt (Atom k) ms <- encs, 
>                               member (inverse1 fiks k) allargs]
>        ++
>        [Encrypt (Apply f as) ms | 
>           Encrypt (Apply f as) ms <- encs, 
>           canApplyFn fvts fnts allargs knows (Apply (inverse1 fiks f) as)]
>      lUnXors = -- Vernam decryptions that can be undone because agent 
>                 -- can produce first arg
>        [Xor m m' | Xor m m' <- xors, 
>                    canReceiverProduce fvts fnts allargs knows m]
>      rUnXors = -- Vernam decryptions that can be undone because agent 
>                 -- can produce second arg
>        [Xor m m' | Xor m m' <- xors, 
>                    canReceiverProduce fvts fnts allargs knows m']
>  in
>  if ---- Case where at least one decryption can be done
>     unEncs /= [] || lUnXors /= [] || rUnXors /= []
>        -- or [member (inverse1 fiks k) allargs | Encrypt k _ <- encs]
>  then 
>   let decs = -- all messages agent can get through [Vernam] decrypting
>         concat [ms | Encrypt _ ms <- unEncs] ++
>         concat [unSeq m' | Xor _ m' <- lUnXors] ++
>         concat [unSeq m | Xor m _ <- rUnXors]
>       nodecs = -- messages he can't immediately decrypt
>         [Encrypt k ms | Encrypt k ms <- encs, 
>                         not (member (Encrypt k ms) unEncs)]
>                         -- not (member (inverse2 fiks k) allargs)]
>       nodecxors = -- Vernam encryptions he can't immediately decrypt
>         [m | m <- xors, not (member m (lUnXors ++ rUnXors))]
>       newkeys = -- new held keys used in encryptions 
>         [k | Encrypt (Atom k) _ <- unEncs, 
>              not (member (inverse1 fiks k) args)] 
>         ++
>         [k | Xor m _ <- lUnXors, k <- senderAtoms m, not (member k args)] 
>         ++
>         [k | Xor _ m' <- rUnXors, k <- senderAtoms m', not (member k args)]
>       args' = -- new knowledge
>         sortremdups ([a | Atom a <- decs] ++ args ++ newkeys)
>       encs' = -- nested encrypted components obtained from decrypting 
>               -- outer encryption
>         [Encrypt k ms | Encrypt k ms <- decs]
>       xors' = [Xor m m' | Xor m m' <- decs]
>   in canDecrypt fvts fnts fiks args' knows 
>                  (nodecs ++ encs') (nodecxors ++ xors')
>  else ---- Case where no more components can be decrypted
>       ([k | Encrypt k _ <- encs], 
>        [Xor m m' | Xor m m' <- xors], 
>        args)

Test whether receiver can do particular function application

>canApplyFn fvts fnts allargs knows (Apply f m) = 
>  (knowsFn fnts knows f || member (Apply f m) knows)
>  &&
>  canReceiverProduce fvts fnts allargs knows m

>knowsFn fnts knows f =
>  findFnType1 fnts f == HashFunction || member (Atom f) knows 

Test whether message m can be produced from knowledge of atoms in allargs and
functions in knows, first for sender, then for receiver

>canSenderProduce :: 
>  VarTypeList -> FnTypeList -> [VarName] -> [Msg] -> Msg -> Bool
>canSenderProduce fvts fnts allargs knows m =
>  all ok (senderAtomFns m)
>  where ok (Atom a) = member a allargs || findtype_ fvts a == "TimeStamp"
>        ok (Apply f m') =
>              (findFnType1 fnts f == HashFunction 
>               || member (Apply f m') knows 
>               || member (Atom f) knows)
>              && 
>              canSenderProduce fvts fnts allargs knows m'

>canReceiverProduce :: 
>  VarTypeList -> FnTypeList -> [VarName] -> [Msg] -> Msg -> Bool
>canReceiverProduce fvts fnts allargs knows m =
>  all (canReceiverProduceAtom fvts fnts allargs knows) (receiverAtomFns m)

>canReceiverProduceAtom :: 
>  VarTypeList -> FnTypeList -> [VarName] -> [Msg] -> Msg -> Bool
>canReceiverProduceAtom fvts _ allargs _ (Atom a) = 
>  member a allargs || findtype_ fvts a == "TimeStamp"
>canReceiverProduceAtom fvts fnts allargs knows (Apply f m') = 
>  canApplyFn fvts fnts allargs knows (Apply f m')

Split Sq

>unSeq (Sq ms) = ms
>unSeq m = [m]

=========================================================================

>checkActualSystem fvts procs vts actualAgents = 
>  flatmap (checkTypes fvts procs vts) actualAgents
     
Check that the process (procname, args) matches some process defined earlier,
and the actual variables match the types of the free variables.

>checkTypes fvts procs vts (procname, args) 
>  | matches == []
>      = "Process name " ++ procname ++ " not found\n"
>  | length args /= length args'
>      = "Argument lists of different lengths for process " ++ procname ++ "\n"
>  | otherwise
>      = concat [compareTypes (findtype_ fvts v') (allTypes_ vts v) v | 
>                  (v,v') <- zip args args']
>  where matches = 
>          [args' | (_,procname',args',_,_) <- procs, procname == procname']
>        args' = hd matches

>compareTypes t1 ts2 v = 
>  maybeString (not (member t1 ts2) )
>    ("Argument "++v++" of unexpected type(s) "++commaConcat ts2++
>     "; expected "++t1++"\n")

