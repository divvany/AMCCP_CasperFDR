Produce definitions of types of messages

>module MessageTypes(messageIntTypes, messageExtTypes, messageTypesExported) 
>where

>import Useful
>import Pprint
>import Types
>import Messages
>import Annotated

Produce definitions of types of messages as they are experienced by the
agents.

>messageIntTypes :: Annotated -> Output
>messageIntTypes an =
>  let  Annotated { protdesc = protdes } = an
>  in
>  -- mkEnvMessages an ++ -- ENV_INT_MSG* and ENV_MSG* messages, now exported
>  -- mkINTMessages an ++ -- INT_MSG_INFO* messages, now exported
>  "  -- types of messages sent and received by agents, as they are\n"++
>  "  -- considered by those agents\n\n"++
>  "  input_proj((l_,m_,se_,re_)) = (l_,m_,re_)\n"++
>  "  rmb_input_proj((l_,m_,se_,re_)) = ALGEBRA_M::rmb((l_,m_,re_))\n"++
>  "  output_proj((l_,m_,se_,re_)) = (l_,m_,se_)\n\n"++
>  "  INPUT_INT_MSG :: {(Labels, Encryption, <Encryption>)}\n"++
>  "  INPUT_INT_MSG = \n    " ++
>  makeUnion 4 
>    ["INPUT_INT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes]++
>  "\n" ++
>  "  OUTPUT_INT_MSG :: {(Labels, Encryption, <Encryption>)}\n"++
>  "  OUTPUT_INT_MSG = \n    " ++
>  makeUnion 4 ["OUTPUT_INT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes]++ 
>  "\n" 

Create the sets of messages ENV_INT_MSG* and ENV_MSG*, corresponding to
environment messages

>mkEnvMessages an = 
>  let  envmsgnos = 
>        [n | (_,n,Environment,_,_,_,_,_) <- protdes] ++
>        [n | (_,n,_,Environment,_,_,_,_) <- protdes]
>       Annotated { protdesc = protdes } = an
>  in
>  "  -- Environmental messages\n\n"++
>  concat -- received environment messages
>    [let ls = -- getExtra extraInfo_env n ++
>              re++(if nowNeeded then ["now"] else [])
>     in "  ENV_INT_MSG"++n++" :: {(Labels, Encryption, <Encryption>)}\n"++
>	 "  ENV_INT_MSG"++n++" = \n    {(Env"++n++", " ++  
>        showMsg an m ++", <" ++ commaConcat ls ++ ">) |\n       " ++ 
>        makegens (fvts an) (dtdefs an) (remdups((atoms m)++ls)) ++ "}\n" |
>          (_,n,Environment,Agent _,m,(_,nowNeeded),_,re) <- protdes] ++
>  concat -- sent environment messages
>    [--let ls = [] -- getExtra extraInfo_env n
>     "  ENV_INT_MSG"++n++" :: {(Labels, Encryption, <Encryption>)}\n"++
>     "  ENV_INT_MSG"++n++" = \n    {(Env"++n++", "++
>        showMsg an (varMsg m)++
>        ", <"++commaConcat se++">) |\n       "++ 
>        format 7 ", " 
>         (makeVarGens an (remdups(varFields2 se++varFields m)))
>        ++ "}\n" |
>         (_,n,Agent _,Environment,m,_,se,_) <- protdes] ++
>  "\n"++
>  concat -- renamed environment messages
>    ["  ENV_MSG"++n++" = {ALGEBRA_M::rmb(m_) | m_ <- ENV_INT_MSG"++n++"}\n"| 
>       n <- envmsgnos] ++
>  "\n"++
>  "  ENV_INT_MSG :: {(Labels, Encryption, <Encryption>)}\n"++
>  "  ENV_INT_MSG = " ++
>  (if envmsgnos == [] then "{(Env0, Garbage, <>)}"
>   else makeUnion 4 ["ENV_INT_MSG"++n | n <- envmsgnos]) ++ 
>  "\n"

Create the sets of INT_MSG_INFO* messages

>mkINTMessages an = 
>  let  Annotated { protdesc = protdes } = an
>  in 
>  "  -- information about messages sent and received by agents, including\n"++
>  "  -- extras fields for both agents\n\n"++
>  concat 
>    [mkINTMessage an (n,m,se,re) | 
>       (_,n,Agent _,Agent _,m,_,se,re) <- protdes] ++
>  "\n"

Create a single INT_MSG_INFO* message (and maybe the corresponding
INT_MSG_INFO*_0 message).

>mkINTMessage an (n,m,se,re) = 
>  let clash_fields = se \\ atomsRec m
>      re_renamed = [if elem v clash_fields then v++"_X_" else v | v <- re]
>      mVarFields = varFields m
>      mSubstVars = [v | Subst v m <- mVarFields]
>      extra_vars = [v | v <- se++re_renamed, v `notElem` mSubstVars]
>      vars = remdups (varFields2 extra_vars++mVarFields)
>  in "  INT_MSG_INFO"++n++ (ifFlagString an UnboundedParallel "_0") ++" = \n"++
>     "    {(Msg"++n++", " ++                   -- message number
>     showMsg an (varMsg m) ++         -- message body
>     ", <"++commaConcat se++">, "++      -- sender extras
>     "<"++commaConcat re_renamed++">) |\n"++      -- receiver extras
>     "       "++
>     format 7 ", " (makeVarGens an vars) -- generators
>     ++ "}\n" ++
>     maybeString (hasFlag an UnboundedParallel)
>       ("  INT_MSG_INFO"++n++" = \n"++
>        "    {(Msg"++n++", m, s, r) | (Msg"++n++",m,s,r) <- INT_MSG_INFO"++
>        n++"_0,\n"++
>        "      member(m,INTRUDER_M::KnowableFact)}\n")



Produce definitions of message types as they appear on the network

>messageExtTypes :: Annotated -> Output
>messageExtTypes an =
>  "  -- Messages as they appear on the network; each messages is renamed\n"++
>  "  -- (by rmb) to the representative member of its equivalence class\n\n"++
>  concat
>    ["  INPUT_MSG"++n++" = {ALGEBRA_M::rmb(m_) | m_ <- INPUT_INT_MSG"++ n ++ "}\n" |
>        (_,n,Agent _,Agent _,_,_,_,_)<-protdesc an] ++
>  "\n"++
>  concat
>    ["  OUTPUT_MSG"++n++" = {ALGEBRA_M::rmb(m_) | m_ <- OUTPUT_INT_MSG"++n++"}\n"
>        | (_,n,Agent _,Agent _,_,_,_,_)<-protdesc an] ++
>  "\n"++
>  concat
>    ["  DIRECT_MSG"++n++" = {ALGEBRA_M::rmb4(m_) | m_ <- INT_MSG_INFO"++n++"}\n"
>        | (_,n,Agent _,Agent _,_,_,_,_)<-protdesc an] ++
>  "\n"

Produce definitions of types of messages that are exported from this module

>messageTypesExported :: Annotated -> Output
>messageTypesExported an =
>  let  Annotated { protdesc = protdes } = an
>  in
>  mkEnvMessages an ++ -- ENV_INT_MSG* and ENV_MSG* messages
>  mkINTMessages an ++ 
>  "  ENV_MSG = {ALGEBRA_M::rmb(m_) | m_ <- ENV_INT_MSG}\n\n" 
>  ++ 
>  "  INT_MSG_INFO :: {(Labels, Encryption, <Encryption>, <Encryption>)}\n"++
>  "  INT_MSG_INFO = " ++
>  makeUnion 4 ["INT_MSG_INFO"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdesc an]
>  ++
>  concat
>    ["  INPUT_INT_MSG"++n++" = "++
>        "{ input_proj(mt_) | mt_ <- INT_MSG_INFO"++n++" }\n" |
>          (_,n,Agent _,Agent _,_,_,_,_) <- protdes] ++
>  "\n"++
>  "  INPUT_MSG = " ++
>  makeUnion 4 ["INPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdesc an]
>  ++
>  concat
>    ["  OUTPUT_INT_MSG"++n++" = "++
>       "{ output_proj(mt_) | mt_ <- INT_MSG_INFO"++n++" }\n" |
>          (_,n,Agent _,Agent _,_,_,_,_) <- protdes] ++
>  "\n"++
>  "  OUTPUT_MSG = " ++
>  makeUnion 4 ["OUTPUT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdesc an]
>  ++
>  "  DIRECT_MSG = " ++
>  makeUnion 2 ["DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdesc an]++
>  "\n"++
>  if sessinfo an /= [] then
>    "  channel input:ALL_PRINCIPALS.ALL_PRINCIPALS.SessionIds.INPUT_INT_MSG\n" ++
>    "  channel output: ALL_PRINCIPALS.ALL_PRINCIPALS.SessionIds.OUTPUT_INT_MSG\n" ++
>    "  channel env_I : ALL_PRINCIPALS.ENV_INT_MSG\n" ++
>    (if filter ((== 1) . (\ (a,b,c) -> b)) (sessinfo an) /= [] then
>      "  channel allocate : ALL_PRINCIPALS.SessionIds"
>     else "") ++ 
>    (if filter ((== 2) . (\ (a,b,c) -> b)) (sessinfo an) /= [] then
>      "  channel pair : SessionIds.SessionIds"
>     else "") ++"\n\n"
>  else
>    "  channel input:ALL_PRINCIPALS.ALL_PRINCIPALS.INPUT_INT_MSG\n" ++
>    "  channel output: ALL_PRINCIPALS.ALL_PRINCIPALS.OUTPUT_INT_MSG\n" ++
>    "  channel env_I : ALL_PRINCIPALS.ENV_INT_MSG\n\n"
