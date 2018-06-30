>module SimpTypeCheck (simptypecheck)
>where
>import Useful
>import Atoms
>import Messages
>import SimpTypes

>simptypecheck :: VarTypeList -> FnTypeList -> Simpls -> String
>simptypecheck fvts fnts simpls = flatmap (checkSimpl fvts fnts) simpls


>checkSimpl :: VarTypeList -> FnTypeList -> Simpl -> String
>checkSimpl fvts fnts (RemoveFields ts) = flatmap (isType fvts fnts) ts

>checkSimpl _ _ (RemoveHash m) = 
>		if noPerCents m -- == True
>		then ""
>		else "No matching message : RemoveHash msg" ++"\n"

>checkSimpl _ _ (RemoveEncryption m) = 
>		if noPerCents m -- == True
>		then ""
>		else "No matching message : RemoveEncryption msg"  ++"\n"

>checkSimpl fvts fnts (SwapPairs (t1,t2)) = 
>				isType fvts fnts t1 ++ isType fvts fnts t2
 
>checkSimpl fvts fnts(Coalesce ts) = flatmap (isType fvts fnts) ts

>checkSimpl _ _ (RemoveHashedFields m) =
>  if noPerCents m==True
>  then ""
>  else "No matching message : RemoveHashedFields msg" ++"\n"

>checkSimpl _ _ (RemovePlainAndEnc ) = ""


>isType :: VarTypeList -> FnTypeList -> TypeName -> String

>isType fvts fnts tn = 
>   if or [t==tn | (_,t,_)  <- fvts] || or [vt==tn |(_,Defed _ vt) <- fnts] 
>   then  ""
>   else "No variable matches "++ tn



