>module Messages (
>  -- messages
>  Msg(Atom, Encrypt, Sq, Xor, Undec, Forwd, Apply, Sent), funname,
>  findtype2, atomsSend, atomsRec, atomsSend_accum,
>  atomsRec_accum, atoms, senderAtomFns, receiverAtomFns, fnApps,
>  receiverfnApps, VarField(Simple, Subst), fnPerCents,
>  receiverPerCents, noPerCents, receiverFields, 
>  senderFields, receiver2Fields, varFields, varFields2, senderAtoms,
>  senderTimeStamps, keys, anyOfTypes, receiverKeys, receiverMsg,
>  senderMsg, varMsg, patternMatchable, showMsg_,
>  showSenderMsg_, showReceiverMsg_, showReceiverChanMsg, showFn,
>  showPatMsg, components1, typeSet_, makegen, makegens, makeVarGens_,
>  TaggedVarName(Percent, Free), secTypeSet_, typeSetNoGarbage_, 
>  newNames, makeRIGens
>  ) 
>where

>import Useful
>import Pprint
>import Atoms

=========================================================================
Protocol messages

>data Msg = Atom VarName | Encrypt Msg [Msg] | Sq [Msg] | Xor Msg Msg |
>           Undec Msg VarName | Forwd VarName Msg | Apply VarName Msg | 
>           Sent Msg [Msg]
>           deriving (Eq, Ord, Show)

Undecryptable k ms enc represents a message {ms}{k} that the receiver cannot
decrypt, but which he stores in the variable enc.  Forward enc k ms represents
a message stored in enc which is to be forwarded and interpreted as being of
the form {ms}{k}.

function to produce the datatype constructor representing a symbolic function

>funname f = f++"__"

=====================================================================

Find type of a message that should be atomic

>findtype2 :: VarTypeList -> FnTypeList -> Msg -> VarName
>findtype2 fvts _ (Atom a) = findtype_ fvts a
>findtype2 _ fnts (Apply f _) = findFnRanType fnts f
>findtype2 fvts fnts (Forwd _ m) = findtype2 fvts fnts m
>findtype2 fvts fnts (Undec m _) = findtype2 fvts fnts m
>findtype2 _ _ m = error ("findtype2: "++show m)

=========================================================================

return atoms of message, sorted, with no duplicates

>atoms :: Msg -> [VarName]
>atoms (Atom v) = [v]
>atoms (Encrypt k ms) = sortremdupsconcat (atoms k : map atoms ms)
>atoms (Sq ms) = sortremdupsconcat (map atoms ms)
>atoms (Xor m m') = remdupsmerge (atoms m) (atoms m')
>atoms (Undec m _) = atoms m
>atoms (Forwd _ m) = atoms m
>atoms (Apply _ m) = atoms m

return atoms of message which are visible to the sender sorted, with
no duplicates.

>atomsSend :: Msg -> [VarName]
>atomsSend (Atom v) = [v]
>atomsSend (Encrypt k ms) = sortremdupsconcat (atomsSend k : map atomsSend ms)
>atomsSend (Sq ms) = sortremdupsconcat (map atomsSend ms)
>atomsSend (Xor m m') = remdupsmerge (atomsSend m) (atomsSend m')
>atomsSend (Undec m _) = atomsSend m
>atomsSend (Forwd v _) = [v]
>atomsSend (Apply _ m) = atomsSend m

return atoms of message which are visible to the receiver, sorted,
with no duplicates.

>atomsRec :: Msg -> [VarName]
>atomsRec (Atom v) = [v]
>atomsRec (Encrypt k ms) = sortremdupsconcat (atomsRec k : map atomsRec ms)
>atomsRec (Sq ms) = sortremdupsconcat (map atomsRec ms)
>atomsRec (Xor m m') = remdupsmerge (atomsRec m) (atomsRec m')
>atomsRec (Undec _ v) = [v]
>atomsRec (Forwd _ m) = atomsRec m
>atomsRec (Apply _ m) = atomsRec m

return set of function applications sorted, with no duplicates

>fnApps :: Msg -> [(VarName, Msg)]
>fnApps (Atom _) = []
>fnApps (Encrypt k ms) = sortremdupsconcat (fnApps k : map fnApps ms)
>fnApps (Sq ms) = sortremdupsconcat (map fnApps ms)
>fnApps (Xor m m') = remdupsmerge (fnApps m) (fnApps m')
>fnApps (Undec m _) = fnApps m
>fnApps (Forwd _ m) = fnApps m
>fnApps (Apply f m) = [(f, m)] 

Function applications as seen by receiver, excluding keys

>receiverfnApps :: Msg -> [(VarName, Msg)]
>receiverfnApps (Atom _) = []
>receiverfnApps (Encrypt _ ms) = sortremdupsconcat (map receiverfnApps ms)
>receiverfnApps (Sq ms) = sortremdupsconcat (map receiverfnApps ms)
>receiverfnApps (Xor m m') = remdupsmerge (receiverfnApps m) (receiverfnApps m')
>receiverfnApps (Undec _ _) = [] -- receiverfnApps m
>receiverfnApps (Forwd _ m) = receiverfnApps m
>receiverfnApps (Apply f m) = [(f, m)] 

>data VarField = Simple VarName | Subst VarName Msg
>                deriving (Eq, Ord, Show)

>data TaggedVarName = Percent VarName | Free VarName
>			deriving (Eq, Ord, Show)

>atomsSend_accum :: Msg -> [TaggedVarName]
>atomsSend_accum (Atom v) = [Free v]
>atomsSend_accum (Encrypt k ms) = sortremdupsconcat 
>				(atomsSend_accum k : map atomsSend_accum ms)
>atomsSend_accum (Sq ms) = sortremdupsconcat (map atomsSend_accum ms)
>atomsSend_accum (Xor m m') = remdupsmerge (atomsSend_accum m) 
>					(atomsSend_accum m')
>atomsSend_accum (Undec m _) = atomsSend_accum m
>atomsSend_accum (Forwd v _) = [Free v]
>atomsSend_accum (Apply _ m) = atomsSend_accum m


>atomsRec_accum :: Msg -> [TaggedVarName]
>atomsRec_accum (Atom v) = [Free v]
>atomsRec_accum (Encrypt k ms) = sortremdupsconcat (atomsRec_accum k : 
>						   map atomsRec_accum ms)
>atomsRec_accum (Sq ms) = sortremdupsconcat (map atomsRec_accum ms)
>atomsRec_accum (Xor m m') = remdupsmerge (atomsRec_accum m)
>					 (atomsRec_accum m')
>atomsRec_accum (Undec m _) = [Percent v | v <- atoms m]
>atomsRec_accum (Forwd _ m) = atomsRec_accum m
>atomsRec_accum (Apply _ m) = atomsRec_accum m

Return function-varaible pairs used in %-terms

>fnPerCents :: Msg -> [(VarName, VarName)]
>fnPerCents (Atom _) = []
>fnPerCents (Encrypt k ms) = fnPerCents k ++ flatmap fnPerCents ms
>fnPerCents (Sq ms) = flatmap fnPerCents ms
>fnPerCents (Xor m m') = fnPerCents m ++ fnPerCents m'
>fnPerCents (Undec m v) = 
>  case m of
>    Apply f _ -> [(f,v)]
>    _ -> fnPerCents m
>fnPerCents (Forwd v m) = 
>  case m of
>    Apply f _ -> [(f,v)]
>    _ -> fnPerCents m
>fnPerCents (Apply _ _) = []

List of variables appearing on RHSs of % constructs

>receiverPerCents :: Msg -> [String]
>receiverPerCents (Atom _) = []
>receiverPerCents (Encrypt _ ms) = flatmap receiverPerCents ms
>receiverPerCents (Sq ms) = flatmap receiverPerCents ms
>receiverPerCents (Xor m m') = receiverPerCents m ++ receiverPerCents m'
>receiverPerCents (Undec _ v) = [v]
>receiverPerCents (Forwd _ m) = receiverPerCents m
>receiverPerCents (Apply _ m) = receiverPerCents m

Is a message free from %-s

>noPerCents :: Msg -> Bool
>noPerCents (Atom _) = True
>noPerCents (Encrypt _ ms) = all noPerCents ms
>noPerCents (Sq ms) = all noPerCents ms
>noPerCents (Xor m m') = noPerCents m && noPerCents m'
>noPerCents (Undec _ _) = False
>noPerCents (Forwd _ _) = False
>noPerCents (Apply _ m) = noPerCents m


fnPerCents m

Return set of fields, as seen by receiver

>receiverFields :: Msg -> [VarField]
>receiverFields (Atom v) = [Simple v]
>receiverFields (Encrypt _ ms) = sortremdupsconcat (map receiverFields ms)
>receiverFields (Sq ms) = sortremdupsconcat (map receiverFields ms)
>receiverFields (Xor m m') = 
>  remdupsmerge (receiverFields m) (receiverFields m')
>receiverFields (Undec m v) = [Subst v m]
>receiverFields (Forwd _ m) = receiverFields m
>receiverFields (Apply _ _) = []

>receiver2Fields :: Msg -> [VarField]
>receiver2Fields (Atom v) = [Simple v]
>receiver2Fields (Encrypt k ms) = 
>  sortremdupsconcat (receiver2Fields k:map receiver2Fields ms)
>receiver2Fields (Sq ms) = sortremdupsconcat (map receiver2Fields ms)
>receiver2Fields (Xor m m') = 
>  remdupsmerge (receiver2Fields m) (receiver2Fields m')
>receiver2Fields (Undec m v) = [Subst v m]
>receiver2Fields (Forwd _ m) = receiver2Fields m
>receiver2Fields (Apply _ m) = receiver2Fields m

Return set of fields, including keys

>varFields :: Msg -> [VarField]
>varFields (Atom v) = [Simple v]
>varFields (Encrypt k ms) = sortremdupsconcat (varFields k : map varFields ms)
>varFields (Sent m ms) = sortremdupsconcat (varFields m : map varFields ms)
>varFields (Sq ms) = sortremdupsconcat (map varFields ms)
>varFields (Xor m m') = remdupsmerge (varFields m) (varFields m')
>varFields (Undec m v) = [Subst v m]
>varFields (Forwd v m) = [Subst v m]
>varFields (Apply _ m) = varFields m 

Returns set of fields, as seen by Sender

>senderFields :: Msg -> [VarField]
>senderFields (Atom v) = [Simple v]
>senderFields (Encrypt k ms) = sortremdupsconcat 
>			         (senderFields k : map senderFields ms)
>senderFields (Sq ms) = sortremdupsconcat (map senderFields ms)
>senderFields (Xor m m') = remdupsmerge (senderFields m) (senderFields m')
>senderFields (Undec m _) = senderFields m
>senderFields (Forwd v m) = [Subst v m]
>senderFields (Apply _ m) = senderFields m 
>senderFields (Sent m ms) = sortremdupsconcat (senderFields m : map varFields ms)

Same as varFields above except on a list of 'extra' variables

>varFields2 :: [String] -> [VarField]
>varFields2 [] = []
>varFields2 (x:xs) = Simple x:varFields2 xs

Does agent's identity id appear in message in pattern-matchable way?

>patternMatchable :: AgentId -> Msg -> Bool
>patternMatchable id (Atom v) = id == v
>patternMatchable id (Encrypt _ ms) = any (patternMatchable id) ms
>patternMatchable id (Sq ms)  = any (patternMatchable id) ms
>patternMatchable id (Xor m m') = 
>  patternMatchable id m || patternMatchable id m'
>patternMatchable _ (Undec _ _) = False -- patternMatchable id m
>patternMatchable _ (Forwd _ _) = False -- patternMatchable id m
>patternMatchable _ (Apply _ _) = False

Atoms, from sender's point of view

>senderAtoms :: Msg -> [VarName]
>senderAtoms (Atom v) = [v]
>senderAtoms (Encrypt k ms) = 
>  sortremdupsconcat (senderAtoms k : map senderAtoms ms)
>senderAtoms (Sq ms) = sortremdupsconcat (map senderAtoms ms)
>senderAtoms (Xor m m') = remdupsmerge (senderAtoms m) (senderAtoms m')
>senderAtoms (Undec m _) = senderAtoms m
>senderAtoms (Forwd v _) = [v]
>senderAtoms (Apply f m) = f : senderAtoms m

>senderAtomFns :: Msg -> [Msg]
>senderAtomFns (Atom v) = [Atom v]
>senderAtomFns (Encrypt k ms) = 
>  sortremdupsconcat (senderAtomFns k : map senderAtomFns ms)
>senderAtomFns (Sq ms) = sortremdupsconcat (map senderAtomFns ms)
>senderAtomFns (Xor m m') = remdupsmerge (senderAtomFns m) (senderAtomFns m')
>senderAtomFns (Undec m _) = senderAtomFns m
>senderAtomFns (Forwd v _) = [Atom v]
>senderAtomFns (Apply f as) = [Apply f as]

Now from receiver's point of view

>receiverAtomFns :: Msg -> [Msg]
>receiverAtomFns (Atom v) = [Atom v]
>receiverAtomFns (Encrypt k ms) = 
>  sortremdupsconcat (receiverAtomFns k : map receiverAtomFns ms)
>receiverAtomFns (Sq ms) = sortremdupsconcat (map receiverAtomFns ms)
>receiverAtomFns (Xor m m') = 
>  remdupsmerge (receiverAtomFns m) (receiverAtomFns m')
>receiverAtomFns (Undec _ v) = [Atom v]
>receiverAtomFns (Forwd _ m) = receiverAtomFns m
>receiverAtomFns (Apply f as) = [Apply f as]

return keys used for encrypting parts of message

>keys (Atom _) = []
>keys (Encrypt k ms) = sortremdupsconcat ([k] : map keys ms)
>keys (Sq ms) = sortremdupsconcat (map keys ms)
>keys (Xor m m') = remdupsmerge (keys m) (keys m')
>keys (Undec m _) = keys m
>keys (Forwd _ m) = keys m
>keys (Apply _ _) = []

List of timestamps appearing in message, from sender's point of view

>senderTimeStamps :: VarTypeList -> FnTypeList -> Msg -> [VarName]
>senderTimeStamps fvts _ (Atom v) = 
>  if findtype_ fvts v == "TimeStamp" then [v] else []
>senderTimeStamps fvts fnts (Encrypt _ ms) = 
>  sortremdupsconcat (map (senderTimeStamps fvts fnts) ms)
>senderTimeStamps fvts fnts (Sq ms) = 
>  sortremdupsconcat (map (senderTimeStamps fvts fnts) ms)
>senderTimeStamps fvts fnts (Xor m m') =
>  remdupsmerge (senderTimeStamps fvts fnts m) (senderTimeStamps fvts fnts m') 
>senderTimeStamps fvts fnts (Undec m _) = senderTimeStamps fvts fnts m
>senderTimeStamps _ _ (Forwd _ _) = []
>senderTimeStamps fvts fnts (Apply f m) = 
>  if isHashFunction fnts f then senderTimeStamps fvts fnts m else [] 

Test whether message uses any field of a type from ts

>anyOfTypes :: VarTypeList -> FnTypeList -> [TypeName] -> Msg -> Bool
>anyOfTypes fvts _ ts (Atom a) = member (findtype_ fvts a) ts
>anyOfTypes fvts fnts ts (Encrypt k ms) =
>  anyOfTypes fvts fnts ts k || any (anyOfTypes fvts fnts ts) ms
>anyOfTypes fvts fnts ts (Sq ms) = any (anyOfTypes fvts fnts ts) ms
>anyOfTypes fvts fnts ts (Xor m m') = 
>  anyOfTypes fvts fnts ts m || anyOfTypes fvts fnts ts m'
>anyOfTypes fvts fnts ts (Undec m _) = anyOfTypes fvts fnts ts m
>anyOfTypes fvts fnts ts (Forwd _ m) = anyOfTypes fvts fnts ts m
>anyOfTypes fvts fnts ts (Apply f m) = 
>  not (isHashFunction fnts f) && member (findFnRanType fnts f) ts 
>  || anyOfTypes fvts fnts ts m


>receiverKeys (Atom _) = []
>receiverKeys (Encrypt k ms) = sortremdupsconcat ([k] : map receiverKeys ms)
>receiverKeys (Sq ms) = sortremdupsconcat (map receiverKeys ms)
>receiverKeys (Xor m m') = remdupsmerge (receiverKeys m) (receiverKeys m')
>receiverKeys (Undec _ _) = []
>receiverKeys (Forwd _ m) = receiverKeys m
>receiverKeys (Apply _ _) = []

Message as experienced by sender

>senderMsg :: Msg -> Msg
>senderMsg (Atom v) = Atom v
>senderMsg (Encrypt k ms) = Encrypt (senderMsg k) (map senderMsg ms)
>senderMsg (Sq ms) = Sq (map senderMsg ms)
>senderMsg (Xor m m') = Xor (senderMsg m) (senderMsg m')
>senderMsg (Undec m _) = senderMsg m
>senderMsg (Forwd v _) = Atom v
>senderMsg (Apply f as) = Apply f (senderMsg as) -- as, changed 2013.11.19
>senderMsg (Sent m ms) = Sent (senderMsg m) (map receiverMsg ms)

Message as experienced by receiver

>receiverMsg :: Msg -> Msg
>receiverMsg (Atom v) = Atom v
>receiverMsg (Encrypt k ms) = Encrypt (receiverMsg k) (map receiverMsg ms)
>receiverMsg (Sq ms) = Sq (map receiverMsg ms)
>receiverMsg (Xor m m') = Xor (receiverMsg m) (receiverMsg m')
>receiverMsg (Undec _ v) = Atom v
>receiverMsg (Forwd _ m) = receiverMsg m
>receiverMsg (Apply f as) = Apply f as
>receiverMsg (Sent m ms) = Sent (receiverMsg m) (map receiverMsg ms)

Message with variables in % cases

>varMsg :: Msg -> Msg
>varMsg (Atom v) = Atom v
>varMsg (Encrypt k ms) = Encrypt (varMsg k) (map varMsg ms)
>varMsg (Sq ms) = Sq (map varMsg ms)
>varMsg (Xor m m') = Xor (varMsg m) (varMsg m')
>varMsg (Undec _ v) = Atom v
>varMsg (Forwd v _) = Atom v
>varMsg (Apply f m) = Apply f (varMsg m)
>varMsg (Sent m ms) = Sent (varMsg m) (map varMsg ms)

============================= Printing functions

Print function application or hash function; argument showArgsFn is the
function to be used to print each argument. If expand is called then the
function is evaluated (now) instead. (This allows functions to be on the
LHS of generators <-.)

>showFnExpand fnts showArgsFn (Apply f m) =
>  if isHashFunction fnts f 
>  then "Hash.("++f++", <"++showArgs showArgsFn m++">)"
>  else case findFnType1 fnts f of
>           -- FIXME: could be done by renaming rhs according to args and m
>           Symb dom r  -> f++"__.("++showArgs showArgsFn m++")"
>           _           -> error ("showFnExpand: cannot expand function")
>           -- _           -> error ("showFnExpand: cannot expand function")
>showFnExpand _ _ m = error ("showFn: "++show m)

>showFn fnts showArgsFn (Apply f m) = 
>  if isHashFunction fnts f 
>  then "Hash.("++f++", <"++showArgs showArgsFn m++">)"
>  else f++"("++showArgs showArgsFn m++")"
>showFn _ _ m = error ("showFn: "++show m)

>showArgs showArgsFn (Sq ms) = commaConcat (map showArgsFn ms)
>showArgs showArgsFn m = showArgsFn m

Return string representing message, tagging timestamps as such

>showMsg_ :: VarTypeList -> FnTypeList -> Msg -> String
>showMsg_ fvts _ (Atom v) = 
>  if findtype_ fvts v == "TimeStamp" then "Timestamp."++v else v
>showMsg_ fvts fnts (Encrypt k ms) = 
>  "Encrypt.(" ++ showMsg_ fvts fnts k ++ ", <" ++ 
>  commaConcat (map (showMsg_ fvts fnts) ms) ++ ">)"
>showMsg_ fvts fnts (Sq ms) = 
>  "Sq.<" ++ commaConcat (map (showMsg_ fvts fnts) ms) ++ ">"
>showMsg_ fvts fnts (Xor m m') =  
>  "Xor.(" ++ showMsg_ fvts fnts m ++ ", " ++ showMsg_ fvts fnts m' ++ ")"
>showMsg_ fvts fnts (Undec m _) = showMsg_ fvts fnts m
>showMsg_ fvts fnts (Forwd _ m) = showMsg_ fvts fnts m
>showMsg_ fvts fnts (Apply f m) = showFnExpand fnts (showMsg_ fvts fnts) (Apply f m)
>showMsg_ fvts fnts (Sent m ms) = "Sent.(" ++ showMsg_ fvts fnts m ++ ", <" ++ commaConcat (map (showMsg_ fvts fnts) ms) ++ ">)"

message as seen by sender

>showSenderMsg_ :: VarTypeList -> FnTypeList -> Msg -> String
>showSenderMsg_ fvts fnts = showMsg_ fvts fnts . senderMsg

Message as seen by receiver; used to produce definition of agent process.

>showReceiverMsg_ :: 
>  VarTypeList -> FnTypeList -> InverseKeyList -> Msg -> String
>showReceiverMsg_ fvts _ _ (Atom v) = 
>  if findtype_ fvts v == "TimeStamp" then "Timestamp."++v else v
>showReceiverMsg_ fvts fnts fiks (Encrypt k ms) =
>  "Encrypt.("++showReceiverKey fvts fnts fiks k++", <" ++ 
>  commaConcat (map (showReceiverMsg_ fvts fnts fiks) ms) ++ ">)"
>showReceiverMsg_ fvts fnts fiks (Sq ms) = 
>  "Sq.<" ++ commaConcat (map (showReceiverMsg_ fvts fnts fiks) ms) ++ ">"
>showReceiverMsg_ fvts fnts fiks (Xor m m') = 
>  "Xor.(" ++ showReceiverMsg_ fvts fnts fiks m ++ ", " 
>          ++ showReceiverMsg_ fvts fnts fiks m' ++ ")"
>showReceiverMsg_ _ _ _ (Undec _ v) = v
>showReceiverMsg_ fvts fnts fiks (Forwd _ m) = showReceiverMsg_ fvts fnts fiks m
>showReceiverMsg_ fvts fnts fiks (Apply f m) = 
>  showFnExpand fnts (showReceiverMsg_ fvts fnts fiks) (Apply f m)

Message as seen by receiver; used to produce definition of INPUT_INT_MSG

>showReceiverChanMsg :: VarTypeList -> FnTypeList -> Msg -> String
>showReceiverChanMsg fvts _ (Atom v) = 
>  if findtype_ fvts v == "TimeStamp" then "Timestamp."++v else v
>showReceiverChanMsg fvts fnts (Encrypt k ms) =
>  "Encrypt.("++showReceiverChanMsg fvts fnts k++", <" ++ 
>  commaConcat (map (showReceiverChanMsg fvts fnts) ms) ++ ">)"
>showReceiverChanMsg fvts fnts (Sq ms) = 
>  "Sq.<" ++ commaConcat (map (showReceiverChanMsg fvts fnts) ms) ++ ">"
>showReceiverChanMsg fvts fnts (Xor m m') = 
>  "Xor.(" ++ showReceiverChanMsg fvts fnts m ++ ", " 
>          ++ showReceiverChanMsg fvts fnts m' ++ ")"
>showReceiverChanMsg _ _ (Undec _ v) = v
>showReceiverChanMsg fvts fnts (Forwd _ m) = showReceiverChanMsg fvts fnts m
>showReceiverChanMsg fvts fnts (Apply f m) = 
>  showFn fnts (showReceiverChanMsg fvts fnts) (Apply f m)

Show key, as seen by receiver

>showReceiverKey _ _ fiks (Atom k) = 
>  "inverse(" ++ inverse1 fiks k ++ ")"
>showReceiverKey fvts fnts fiks (Apply f as) =
>  showReceiverMsg_ fvts fnts fiks (Apply f as)
>showReceiverKey _ _  fiks (Undec _ k) =
>  "inverse(" ++ inverse1 fiks k ++ ")"
>showReceiverKey fvts fnts fiks (Forwd _ m) =
>  showReceiverKey fvts fnts fiks m
>showReceiverKey _ _ _ m = error ("showReceiverKey: "++show m)


show message, using _ for all fields except first occurance of pat (agent
name) if flag==false, for all fields if flag==true

>showPatMsg :: VarName -> Bool -> Msg -> (Bool,String)
>showPatMsg pat b (Atom v) 
>  | v == pat && not b   = (True,v)
>  | otherwise           = (b,"_")
>showPatMsg pat b (Encrypt _ ms) = 
>  (b', "Encrypt.(_, <" ++ commaConcat sts ++ ">)")
>  where -- (b',kst) = showPatMsg pat b k
>        (b',sts) = showPatSeq pat b ms
>showPatMsg pat b (Sq ms) = 
>  (b', "Sq.<" ++ commaConcat sts ++ ">")
>  where (b',sts) = showPatSeq pat b ms
>showPatMsg pat b (Xor m m') = (b'', "Xor.("++sts++", "++sts'++")")
>  where (b',sts) = showPatMsg pat b m
>        (b'',sts') = showPatMsg pat b' m'
>showPatMsg _ b (Undec _ _) = (b,"_")
>showPatMsg _ b (Forwd _ _) = (b,"_")
>showPatMsg _ b (Apply _ _) = (b, "_") --  f++"("++commaConcat sts++")")
>  -- where (b',sts) = showPatSeq pat b (map Atom as)

>showPatSeq :: VarName -> Bool -> [Msg] -> (Bool,[String])
>showPatSeq _ b [] = (b,[])
>showPatSeq pat b (m:ms) = (b'', st:sts)
>  where (b',st) = showPatMsg pat b m
>        (b'',sts) = showPatSeq pat b' ms


============================================

components of message reachable without doing any decryption, as seen by
receiver.

>components1 (Atom a) = [Atom a]
>components1 (Sq ms) = concat (map components1 ms)
>components1 (Encrypt k ms) = [Encrypt k ms]
>components1 (Xor m m') = [Xor m m']
>components1 (Apply f ms) = [Apply f ms]
>components1 m = error ("components1: "++show m)
> -- components1 (Undecryptable k ms v) = [Atom v]
> -- components1 (Forward v k ms) = [Encrypt k (map receiverMsg ms)]

Print set giving type of message

>typeSetNoGarbage_ :: VarTypeList -> FnTypeList -> DataTypeDefs -> VarName -> Msg -> String
>typeSetNoGarbage_ fvts fnts dtdefs v m = 
>  case [t | (v',t,_) <- fvts, v==v'] of
>    [t] -> t
>    []  -> "{" ++ showMsg_ fvts fnts (varMsg m) ++ " | " ++  
>           commaConcat (makeVarGens_ fvts fnts dtdefs (varFields m)) ++ "}"

>typeSet_ :: VarTypeList -> FnTypeList -> DataTypeDefs -> VarName -> Msg -> String
>typeSet_ fvts fnts dtdefs v m = "addGarbage_("++typeSetNoGarbage_ fvts fnts dtdefs v m++")"

Produce set corresponding to all secrets of shape m

>secTypeSet_ :: VarTypeList -> FnTypeList -> DataTypeDefs -> Msg -> String
>secTypeSet_ fvts _ _ (Atom s) = findtype_ fvts s
>secTypeSet_ _ fnts _ (Apply f _) = findFnRanType fnts f 
>secTypeSet_ fvts fnts dtdefs m = 
>  "{" ++ showMsg_ fvts fnts (varMsg m) ++ " | " ++  
>  commaConcat (makeVarGens_ fvts fnts dtdefs (varFields m)) ++ "}"

>makegens fvts dtdefs = 
>  commaConcat . filter (/= "") . map (makegen fvts dtdefs)

>makegen fvts dtdefs v = 
>  let dtcons0 = [cons | (_,pats,_) <- dtdefs, (cons,[]) <- pats]
>  in
>  if member v dtcons0  -- if v is a datatype constructor...
>  then ""              -- then produce no generator
>  else if take 10 v == "Timestamp." then drop 10 v++" <- TS"
>  else v ++ " <- " ++ findtypeT_ fvts v

>makeVarGens_ fvts fnts dtdefs args = 
>  filter (/= "") (map (makeVarGen fvts fnts dtdefs) args)

>makeVarGen fvts _ dtdefs (Simple v) = 
>  let dtcons0 = [cons | (_,pats,_) <- dtdefs, (cons,[]) <- pats]
>  in
>  if member v dtcons0  -- if v is a datatype constructor...
>  then ""              -- then produce no generator
>  else if take 10 v == "Timestamp." then drop 10 v++" <- TS"
>  else v ++ " <- " ++ findtypeT_ fvts v
>makeVarGen fvts fnts dtdefs (Subst v m) = 
>  v ++ " <- " ++ typeSet_ fvts fnts dtdefs v m

We want to be able to replace each repeated field in a message with a new
name.  Each variable v will be renamed using the following

>rename :: String -> Int -> String
>rename v n = v++"_"++show n++"_"

Each (v, n) in lists of the following type rens means that v has been replaced
by v_k_ for each k in [0..n).

>type RenameIndex = [(String, Int)]

Find the next suffix number to use; -1 means use the variable straight

>lookupRI :: RenameIndex -> String -> Int
>lookupRI rens v = 
>  let matches = [n | (v1,n) <- rens, v==v1]
>  in if matches==[] then -1 else head matches

Update v to be mapped to n

>update :: RenameIndex -> String -> Int -> RenameIndex
>update rens v n = (v, n) : filter ((/= v) . fst) rens

Replace each repeated field in a message with a new name.  Return RenameIndex
showing which variables were replaced.

>newNames :: Msg -> (Msg, RenameIndex)
>newNames m = newNames0 (m, []) 

>newNames0 :: (Msg, RenameIndex) -> (Msg, RenameIndex)
>newNames0 (Atom v, rens) = 
>  let n = lookupRI rens v 
>  in if n == -1 then (Atom v, (v,0):rens)
>     else (Atom (rename v n), update rens v (n+1))
>newNames0 (Encrypt k ms, rens) =
>  let (k', rens') = newNames0 (k, rens)
>      (ms', rens'') = newNamesList (ms, rens')
>  in (Encrypt k' ms', rens'') 
>newNames0 (Sq ms, rens) = 
>  let (ms', rens') = newNamesList (ms, rens) in (Sq ms', rens')
>newNames0 (Apply f m, rens) = 
>  let (m', rens') = newNames0 (m, rens) in (Apply f m', rens')
>newNames0 (Sent m es, rens) = 
>  let (m', rens') = newNames0 (m, rens)
>      (es', rens'') = newNamesList (es, rens')
>  in (Sent m' es', rens'')

Iterate through list of names, replacing each repeated field.

>newNamesList :: ([Msg], RenameIndex) -> ([Msg], RenameIndex)
>newNamesList ([], rens) = ([], rens)
>newNamesList (m:ms, rens) = 
>  let (m', rens') = newNames0 (m, rens)
>      (ms', rens'') = newNamesList (ms, rens')
>  in (m' : ms', rens'')

Make generators corresponding to a RenameIndex

>makeRIGens :: RenameIndex -> [String]
>makeRIGens rens = 
>  [rename v k ++ " == " ++ v | (v,n) <- rens, k <- [0 .. n-1]]