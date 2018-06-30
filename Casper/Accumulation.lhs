>module Accumulation(accumulation, accumulation', accumulation_init)

>where

>import Useful
>import Atoms
>import Messages
>import Types
>import Annotated

** Note this code is now independent of data independence, so can be
tidied up somewhat **

-----------------------------------------------------------------------
accumulation
-----------------------------------------------------------------------

Here we remove the messages where the Environment is either Sender or
Receiver since we know from the Consistency Checking Phase that none
of these messages will be monitored by any managers for DI variables.

>accumulation' :: ProtDesc' -> FreshVarList
>accumulation' protdesc = 
>  let accumInit = 
>        accumulation_init [(n,ass,a,b,m,t) | (n,ass,a,b,m,t,_,_) <- protdesc]
>  in
>      [(nr,(s,sl),(r,rl)) | (nr,(Agent s,sl),(Agent r,rl)) <- accumInit]

>accumulation :: ProtDesc -> FreshVarList
>accumulation protdesc = 
>  let accumInit = accumulation_init  protdesc 
>  in
>      [(nr,(s,sl),(r,rl)) | (nr,(Agent s,sl),(Agent r,rl)) <- accumInit]

-----------------------------------------------------------------------
accumulation_init
-----------------------------------------------------------------------

returns a list providing the information about which fresh values have
been introduced by the sender and which values are new to the
receiver, for each message m in the protocol description.

NOTE:  This function takes all types of senders and receivers into
account. i.e. Both Environment and Agent X types.

We use this resulting list for the consistency check
"checkFreshVarFlow" in Consistency.lhs.

>accumulation_init ::
>  ProtDesc ->			    --  protdesc
>  [(MsgNo,(Player,[VarName]),(Player,[VarName]))]  -- ( accumList )

>--accumulation_init fvts protdesc [] = []
>accumulation_init protdesc = 
>  let	ls = [(nr,(s, atomsSend_accum m),
>                (r, atomsRec_accum m)) | 
>                       (_,nr,s,r,m,_) <- protdesc]
>	ls2 = gatherNewOnly ls
>  in	[(nr,(s,map stripTag sl),(r,map stripTag rl)) | 
>				(nr,(s,sl),(r,rl)) <- ls2,
>				sl/=[] || rl/=[]]
>  where gatherNewOnly [] = []
>        gatherNewOnly (x:xs) = x:gatherNewOnly (f x xs)
>          where f _ [] = []
>                f (n,(s,sl),(r,rl)) ((n2,(s2,sl2),(r2,rl2)):xs) =
>                   (n2,(s2, same (s,sl) (r,rl) (s2,sl2)),
>                       (r2, same (s,sl) (r,rl) (r2,rl2))):
>                          f (n,(s,sl),(r,rl)) xs
>                same (x,xs) (y,ys) (z,zs) = if x==z then 
>						(zs\\(xs\\(percentVals zs))) 
>                                            else if y==z then 
>						(zs\\(ys\\(percentVals zs)))
>                                                 else zs
>	 stripTag (Percent v) = v
>	 stripTag (Free v) = v
>	 percentVals [] = []
>	 percentVals (x:xs) =
>		case x of
>		  Percent _ -> x:percentVals xs
>		  Free _ -> percentVals xs

gatherNewOnly above filters out all values which are present in previous
messages, thus leaving only the fresh values by the sender or new ones
to the receiver.