>module Simplify(simplifications) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import SimpTypes

Process the input file and each simplification in turn

>simplifications :: SimplInputpd -> String

>simplifications (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, 
>						auths, simpls) =
>	"Original protocol:" ++ "\n" ++showpd protdesc ++ 
>       simplifications2 (fvts, fnts, fiks, dtdefs, procs, protdesc, 
>					secrets, auths, simpls)

if the simplification does not match with the protocol description,
then output an error

>check :: ProtDesc -> ProtDesc -> Bool
>check pd pd' = let mix = zip pd pd'
>	        in check1 mix

>check1 :: [(ProtMsgDesc, ProtMsgDesc)] -> Bool
>check1 (((_,_,_,_,m,_),(_,_,_,_,m',_)):pds) = m == m' && check1 pds
>check1 [] = True

>simplifications2 :: SimplInputpd -> String

>simplifications2 (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, 
>						auths, simpl:simpls) =
>	let protdesc' = applySimp (matchSimp fvts fnts simpl) protdesc
>	in if (check protdesc protdesc' == False)
>	   then "\n"++"Simplified protocol description:\n"++showpd protdesc' ++
>           	simplifications2 (fvts, fnts, fiks, dtdefs, procs, protdesc', 
>					secrets, auths, simpls)
>	   else "\n"++"No match simplification" ++ "\n" ++
>               simplifications2 (fvts, fnts, fiks, dtdefs, procs, protdesc', 
>					secrets, auths, simpls)

>simplifications2 (_, _, _, _, _, _, _, _, []) = ""
 
============================================================================

>type Simplification = Msg -> Msg

Apply simplification to all messages of protocol

>applySimp :: Simplification -> ProtDesc -> ProtDesc
>applySimp s pd = [(ass,n,a,b,s m,t) | (ass,n,a,b,m,t) <- pd]

Match the simplification with the corresponding function

>matchSimp :: VarTypeList -> FnTypeList -> Simpl -> Simplification

>matchSimp fvts fnts (RemoveFields ts) = removeFields fvts fnts ts

>matchSimp fvts fnts (RemoveEncryption m) = removeEncryption fvts fnts m

>matchSimp fvts fnts (RemoveHash m) = removeHash fvts fnts m

>matchSimp fvts _ (SwapPairs (t1,t2)) = swapPairs fvts (t1,t2)

>matchSimp fvts _ (Coalesce ts) = coalesce fvts ts


========================================================================
Display protocol description.

This needs tidying up.

>showpd :: ProtDesc -> String
>showpd protdesc = flatmap showpdstep protdesc

>showpdstep(_,n,a,b,m,_) =
>  n ++". "++showPlayer a++" -> "++showPlayer b++" : "++showmsg m++"\n"

>showPlayer Environment = " "
>showPlayer (Agent s) = s

Show individual message; are there enough brackets?

>showmsg :: Msg -> String
>showmsg (Atom v) = v
>showmsg (Encrypt k ms) = 
>  "{"++commaConcat (map showmsg ms) ++ "}{" ++ showmsg k ++ "}" 
>showmsg (Sq ms) = commaConcat (map showmsg ms)
>showmsg (Xor m m') = showmsg m ++ " (+) " ++ showmsg m'
>showmsg (Undec m v) = showmsg m ++ "%" ++ v
>showmsg (Forwd v m) = v ++ "%" ++ showmsg m
>showmsg (Apply f m) = f++"("++showmsg m++")"

=======================================================================
Removing fields simplifying function

>nil = Atom "_Nil"

>removeFields :: VarTypeList -> FnTypeList -> [TypeName] -> Simplification

>removeFields fvts _ ts (Atom a) =
>		if member (findtype_ fvts a) ts
>		then nil
>		else Atom a

>removeFields fvts fnts ts (Encrypt k ms) =
>		let ms' = map (removeFields fvts fnts ts) ms
>		    ms'' = filter (\m -> m /= nil) ms'
>		in if ms'' == []
>		   then nil
>		   else Encrypt k ms''

>removeFields fvts fnts ts (Apply f m) = 
>		if (isHashFunction fnts f)
>		then let m' = removeFields fvts fnts ts m
>                    in if m' == nil
>		        then nil
>		        else Apply f m'
>		else if member(findFnRanType fnts f) ts
>		     then nil 
>		     else Apply f m

>removeFields fvts fnts ts (Undec m v) = 
>		let m' = (removeFields fvts fnts ts) m 
>		in if m' == nil
> 		   then nil
>		   else Undec m' v

>removeFields fvts fnts ts (Forwd v m) = 
>		let m' = (removeFields fvts fnts ts) m
>		in if m' == nil
> 		   then nil
>		   else Forwd v m'

>removeFields fvts fnts ts (Sq ms) = Sq(map (removeFields fvts fnts ts) ms)

=========================================================================
Removing hash functions.

Specifying the hashed message in terms of types
Uses 'sameType' function defined in removing encryptions below

>removeHash :: VarTypeList -> FnTypeList -> Msg ->Simplification
>removeHash fvts fnts (Apply f' m') (Apply f m) =
>		if (isHashFunction fnts f') &&
>		   (isHashFunction fnts f) 
>		then if sameType fvts fnts m' m
>		     then m 
>		     else Apply f(removeHash fvts fnts (Apply f' m') m)
> 		else Apply f m

>removeHash _ _ (Apply _ _) (Atom a) = Atom a

>removeHash fvts fnts (Apply f' m') (Encrypt k ms) = 
>		let m'' = map (removeHash fvts fnts (Apply f' m')) ms
>		in Encrypt k m''

>removeHash fvts fnts (Apply f' m') (Undec m v) = 
>			let m'' = removeHash fvts fnts (Apply f' m') m
>			in Undec m'' v

>removeHash fvts fnts (Apply f' m') (Forwd v m) = 
>			let m'' = removeHash fvts fnts (Apply f' m') m
>			in Forwd v m''

>removeHash fvts fnts (Apply f' m') (Sq ms) = 
>			Sq(map (removeHash fvts fnts (Apply f' m')) ms)

===========================================================================
Removing Encryptions

>removeEncryption :: VarTypeList -> FnTypeList -> Msg -> Simplification

>removeEncryption fvts fnts (Encrypt kt mt) (Encrypt k ms) =
>   if sameType fvts fnts (Encrypt kt mt) (Encrypt k ms)
>   then removeEncryption fvts fnts (Encrypt kt mt) (Sq ms)
>   else let m' = Sq(map(removeEncryption fvts fnts (Encrypt kt mt)) ms)
>        in Encrypt k [m']

removeEncryption fvts fnts (Encrypt kt mt) (Sq ms))

>removeEncryption _ _ _ (Atom a) = Atom a 
>removeEncryption fvts fnts msg (Apply f m) = 
>				Apply f (removeEncryption fvts fnts msg m)
>removeEncryption fvts fnts msg (Undec m v) = 
>		let m' = removeEncryption fvts fnts msg m
>		in Undec m' v 
>removeEncryption fvts fnts msg (Forwd v m) = 
>		let m' = removeEncryption fvts fnts msg m
>		in Forwd v m' 
>removeEncryption fvts fnts msg (Sq ms) = 
>				Sq(map (removeEncryption fvts fnts msg) ms)

To check that the message in the simplification matches with one 
in the protocol description

>sameType :: VarTypeList -> FnTypeList -> Msg -> Msg -> Bool  

>sameType fvts _ (Atom kt) (Atom k) = findtype_ fvts k == kt

>sameType _ fnts (Atom k) (Apply f _) = findFnRanType fnts f == k

>sameType fvts fnts (Sq(mt:mts)) (Sq(m:ms)) = 
>		sameType fvts fnts mt m && sameType fvts fnts (Sq mts) (Sq ms)

>sameType fvts fnts (Encrypt (Atom kt) mt) (Encrypt (Apply vn (Atom n)) ms) =
>			sameType fvts fnts (Atom kt) (Apply vn (Atom n))
>			&& length mt == length ms
>			&& and[sameType fvts fnts t m | (t,m) <- zip mt ms]

>sameType fvts fnts (Encrypt (Atom kt) mt) (Encrypt (Atom k) ms) = 
>				findtype_ fvts k == kt
>			&& length mt == length ms
>			&& and[sameType fvts fnts t m | (t,m) <- zip mt ms]
  
>sameType _ _ (Sq []) (Sq []) = True
>sameType _ _ _ _ = False

==========================================================================
Swapping messages

User specifies which pair types to swap over eg (Nonce, TimeStamp)

>swapPairs :: VarTypeList -> (TypeName,TypeName) -> Simplification
>swapPairs fvts (t1,t2) (Sq ms) = Sq (swapPairsSeq fvts (t1,t2) ms)

>swapPairs _ _ (Atom a) = Atom a
>swapPairs fvts (t1,t2) (Encrypt k ms) = 
>			Encrypt k (swapPairsSeq fvts (t1,t2) ms)
>swapPairs _ _ (Apply f m) = Apply f m
>swapPairs fvts (t1,t2) (Undec m v) =
>				let m' = swapPairs fvts (t1,t2) m
>				in Undec m' v
>swapPairs fvts (t1,t2) (Forwd v m) = 
>				let m' = swapPairs fvts (t1,t2) m
>				in Forwd v m'

Dealing with a sequence of messages

>swapPairsSeq :: VarTypeList -> (TypeName,TypeName) -> [Msg] -> [Msg]
>swapPairsSeq _ _ [] = []
>swapPairsSeq _ _ [m] = [m]
>swapPairsSeq fvts (t1,t2) (Atom a1:Atom a2:ms) 
>	| findtype_ fvts a1 == t1 && 
>	  findtype_ fvts a2 == t2 = (Atom a2 : (swapPairsSeq fvts (t1,t2)
>							(Atom a1:ms)))
>	| otherwise			= (Atom a1 : (swapPairsSeq fvts (t1,t2)
>							(Atom a2:ms)))
>swapPairsSeq fvts (t1,t2) (m1:m2:ms)   = 
>				m1:(swapPairsSeq fvts (t1,t2) (m2:ms))



============================================================================
Coalescing messages

Merging atoms of the same type which are adjacent - coalesced to the left

>coalesce :: VarTypeList -> [TypeName] -> Simplification
>coalesce _ _ (Atom a) = Atom a
>coalesce fvts ts (Encrypt k ms) = Encrypt k (coalesce1 fvts ts ms)
>coalesce fvts ts (Undec m v) = let m' = coalesce fvts ts m
>				in Undec m' v
>coalesce fvts ts (Forwd v m) = let m' = coalesce fvts ts m
>				in Forwd v m'
>coalesce fvts ts (Sq ms) = Sq (coalesce1 fvts ts ms)
>coalesce fvts ts (Apply f m) = Apply f (coalesce fvts ts m)

>coalesce1:: VarTypeList -> [TypeName] -> [Msg] -> [Msg]
>coalesce1 fvts ts (Atom a: Atom b : ms) = 
>				if same fvts (Atom a) (Atom b) 
>				 &&  member(findtype_ fvts a) ts
>				then (Atom a: (coalesce1 fvts ts ms))
>				else (Atom a: (coalesce1 fvts ts (Atom b:ms)))
>			

>coalesce1 fvts ts (m1:ms) = coalesce fvts ts m1:coalesce1 fvts ts ms
>coalesce1 _ _ [] = []
>--coalesce1 fvts ts [m] = [m]
>--coalesce1 fvts [] [m] = [m]

testing if two atoms are of the same type

>same :: VarTypeList -> Msg -> Msg -> Bool
>same fvts (Atom a) (Atom b) = 
>			findtype_ fvts a == findtype_ fvts b


=========================================================================

Removing hashed fields

>removeHashedFields :: VarTypeList -> FnTypeList -> Msg -> Simplification

>removeHashedFields fvts fnts (Apply f' m') (Apply f m) =
>  if (isHashFunction fnts f') && (isHashFunction fnts f)
>  then if sameType fvts fnts m' m then nil
>       else Apply f(removeHashedFields fvts fnts (Apply f' m') m)
>  else Apply f(removeHashedFields fvts fnts (Apply f' m') m)

>removeHashedFields _ _ (Apply _ _) (Atom a) = Atom a

>removeHashedFields fvts fnts (Apply f' m') (Encrypt k ms) =
>  let m'' = map (removeHashedFields fvts fnts (Apply f' m')) ms
>  in Encrypt k m''

>removeHashedFields fvts fnts (Apply f' m') (Undec m v) =
>  let m'' = removeHashedFields fvts fnts (Apply f' m') m
>  in Undec m'' v

>removeHashedFields fvts fnts (Apply f' m') (Forwd v m) =
>  let m'' = removeHashedFields fvts fnts (Apply f' m') m
>  in Forwd v m''

>removeHashedFields fvts fnts (Apply f' m') (Sq ms) =
>  Sq(map (removeHashedFields fvts fnts (Apply f' m')) ms)



=========================================================================

Function to transform (m, {m}_k) to {m}_k

>plainAndEnc :: VarTypeList -> FnTypeList -> Simplification

>plainAndEnc _ _ (Atom a) = Atom a

>plainAndEnc fvts fnts (Apply f m) = Apply f (plainAndEnc fvts fnts m)

>plainAndEnc fvts fnts (Undec m v) = let m'' = plainAndEnc fvts fnts m
>                       in Undec m'' v

>plainAndEnc fvts fnts (Forwd v m) = let m'' = plainAndEnc fvts fnts m
>            in Forwd v m''

>plainAndEnc fvts fnts (Encrypt k ms) =
>   Encrypt k (unSeq(plainAndEnc fvts fnts (Sq(ms))))

>plainAndEnc fvts fnts (Sq [m]) = plainAndEnc fvts fnts m

>plainAndEnc fvts fnts (Sq (m:ms)) =
> f1 [plainAndEnc fvts fnts m] (plainAndEnc fvts fnts (Sq ms))

>unSeq :: Msg -> [Msg]
>unSeq (Sq ms) = ms
>unSeq m = [m]

>f1 :: [Msg] -> Msg -> Msg

>f1 ms (Atom a) = Sq(ms ++ [Atom a])

>f1 ms (Apply f m) = Sq(ms ++ [Apply f m])

>f1 ms (Encrypt k ms') = if ms == ms'
>    then Encrypt k ms'
>    else Sq(ms++[Encrypt k ms'])

>f1 ms (Sq[m]) = f1 ms m

>f1 ms (Sq(Encrypt k ms'':ms')) = if ms == ms''
>      then Sq(Encrypt k ms'':ms')
>      else f1 (ms++ [Encrypt k ms'']) (Sq(ms'))

>f1 ms (Sq(m:ms')) = f1 (ms++[m]) (Sq ms')




