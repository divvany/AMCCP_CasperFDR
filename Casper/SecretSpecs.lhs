Produce specifications, renamed systems, and assertions for secrecy specs.

>module SecretSpecs(
>  makeSecretSpecs
>)
>where

>import Annotated
>import Useful
>import Pprint
>import Types
>import Messages
>import Specs2

>procName :: Annotated -> Argument -> ProcessName
>procName an a = hd [pname' | (a',pname',_,_,_) <- procs an, a==a']

>makeSecretSpecs :: Annotated -> Output
>makeSecretSpecs an =
>  let	secRoles = [procName an a | Sec a _ _ <- secrets an] ++ 
>                  [procName an a  | StrongSec a _ _ <- secrets an]
>       maxSecs = length [proc | SeqComp ps <- actualAgents an, (proc,_) <- ps, 
>                                proc' <- secRoles, proc==proc']
>  in 
>  maybeString (secrets an /= []) (
>    "module SECRET_M\n\n"
>    ++
>    makeSecretSpec an maxSecs
>    ++
>    makeAlpha an
>    ++
>    "exports\n\n"
>    ++
>    ifFlagString an UnboundedParallel (
>    "  (IK, Deductions) =\n"++
>    "   INTRUDER_M::Close_(ALGEBRA_M::applyRenamingToSet(INTRUDER_M::IK0), \n"++
>    "           ALGEBRA_M::applyRenamingToDeductions(INTRUDER_M::Base_Deductions), \n"++
>    "           ALGEBRA_M::applyRenamingToSet(INTRUDER_M::KnowableFact))\n\n"++
>    "  LearnableFact = diff(INTRUDER_M::KnowableFact, IK)\n\n"++
>    "  INTRUDER_0 =\n"++ 
>    "    INTRUDER_M::INTRUDER_00(Deductions,LearnableFact) \\ {|infer"++(ifFlagString an TimestampsUsed ",INTRUDER_M::tockInfer")++"|}\n\n"++
>    "  SYSTEM =\n"++
>    "    SYSTEM_M::SYSTEM_0 [| IntruderInterface |] INTRUDER_M::BUILD_INTRUDER'(INTRUDER_0,IK)\n\n"
>    )
>    ++
>    "  SECRET_SPEC = (|| s_ : ALL_SECRETS @ [AlphaS(s_)] SECRET_SPEC_0(s_))\n\n"
>    ++
>    "  datatype IncInt = IntIn | IntNotIn\n\n"++
>    "  channel scs : ALL_SECRETS.IncInt\n\n"++
>    "  SEQ_SECRET_SPEC = SEQ_SECRET_SPEC_0({})\n\n"
>    ++
>    createSecretRenaming an
>    ++
>    "endmodule\n\n"
>    ++
>    "-- Assertion of secrecy\n\n"++
>    "assert SECRET_M::SECRET_SPEC [T= SECRET_M::SYSTEM_S\n"++
>    "assert SECRET_M::SEQ_SECRET_SPEC [T= SECRET_M::SYSTEM_S_SEQ\n\n")

==========================================================================


=======================================================================
Secrecy specs 

>makeSecretSpec :: Annotated -> Int -> Output
>makeSecretSpec an maxSecs =
>  "  -- Specification for single secret\n\n"++
>  "  SECRET_SPEC_0(s_) = \n" ++
>  "    signal.Claim_Secret?A_!s_?Bs_ ->\n" ++
>  "      (if member("++intruderId an++", Bs_) then SECRET_SPEC_0(s_)\n" ++
>  "       else SECRET_SPEC_1(s_))\n" ++
>  "    []\n" ++
>  "    leak.s_ -> SECRET_SPEC_0(s_)\n" ++
>  ifFlagString an CrackablesUsed (
>     "    []\n"++
>     "    crack?k_ -> SECRET_SPEC_0(s_)\n"
>  ) ++
>  "  SECRET_SPEC_1(s_) = \n"++
>  "    signal.Claim_Secret?A_!s_?Bs_ -> SECRET_SPEC_1(s_)\n" ++  
>  ifFlagString an CrackablesUsed (
>     "    []\n"++
>     "    crack?k_ -> SECRET_SPEC_0(s_)\n"
>  ) ++
>  "  -- Specification for all secrets\n\n"++
>  "  AlphaS(s_) = \n"++
>  "    Union({\n" ++
>  "      {|signal.Claim_Secret.A_.s_ | A_ <- ALL_PRINCIPALS|},\n" ++
>  "      {leak.s_}\n" ++
>  ifFlagString an CrackablesUsed ",\n    {|crack|}" ++
>  "    })\n"++
>  "  -- Sequential version; secs_ is secrets that intruder must not learn\n\n"++
>  "  SEQ_SECRET_SPEC_0(secs_) =\n"++
>  "    scs?s_!IntIn -> SEQ_SECRET_SPEC_0(secs_)\n"++
>  "    []\n"++
>  "    card(secs_)<"++show maxSecs++" & scs?s_!IntNotIn ->\n"++
>  "      SEQ_SECRET_SPEC_0(union(secs_,{s_}))\n"++
>  "    []\n"++
>  "    card(secs_)=="++show maxSecs++" & scs?s_:secs_!IntNotIn ->\n"++
>  "      SEQ_SECRET_SPEC_0(secs_)\n"++
>  "    []\n"++
>  "    leak?s_ : diff(ALL_SECRETS,secs_) -> SEQ_SECRET_SPEC_0(secs_)\n"++
>  ifFlagString an CrackablesUsed (
>     "    []\n    crack?k_ -> SEQ_SECRET_SPEC_0(diff(secs_,{k_}))\n")++
>  "\n"++
>  "  isIntIn(S_) = if member("++intruderId an++",S_) then IntIn else IntNotIn\n\n"

======================================================================
Create renaming for refinement checking

Auxilliary function to remove duplicates from a list of generators, giving
priority to "Subst" fields

>remdups1 :: [VarField] -> [VarField]
>remdups1 gens = 
>  let substs = [Subst v m | Subst v m <- gens]
>      noSubst v =  -- v doesn't appear in a Subst in gens
>        [v | Subst v' m <- substs, v'==v] == []
>      simples = [Simple v | Simple v <- gens, noSubst v]
>  in remdups (substs ++ simples)

>createSecretRenaming :: Annotated -> Output
>createSecretRenaming an  =
>   let (_,authC,directC) = channels an
>       extrainfo = remdups (
>           concat [getId(s,r)++extra an nr id | (nr,id,_,_) <- secretsignals an,
>               (_,n,s,r,_,_,_,_) <- protdesc an,n==nr])
>       genVars = remdups1 (varFields2 extrainfo ++ 
>           (concat [if s==Agent id then senderFields m
>                   else receiver2Fields m | 
>                           (_,nr,s,_,m,_,_,_) <- protdesc an,
>                           (n,id,_,_) <- secretsignals an, n==nr] ))
>       getType1 v = -- deal correctly with timestamps
>         let t = findtypeT an v in if t=="TS" then "TimeStamp" else t
>       renameTypes = remdups [getType1 v | Simple v <- genVars]
>       -- create generators for the two renamings
>       range = format 12 ", " (makeVarGensRM an genVars)
>       sessString = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>       messageSpaceMembership = 
>         remdups (map (messageSetReduction an) (secretsignals an))
>       gens2 = -- some more generators
>         maybeString
>          (hasFlag an UnboundedParallel && messageSpaceMembership /= []) 
>          (",\n        " ++ format 8 ", " messageSpaceMembership)
>       allGens = -- all the generators in the renaming
>         " |\n            " ++range++sessString++gens2++"\n      ]] "
>       hideString = -- string to hide relevant events
>        "\\ {| env, send, receive"++
>        (ifFlagString an TimeUsed ", tock")++
>        (maybeString (directC /= Some[] && authC /= All) ", comm")++
>        (ifFlagString an GuessablesUsed 
>           ", INTRUDER_M::guess, INTRUDER_M::verify")++
>        (ifFlagString an CrackablesUsed ", close")++" |}\n\n"
>   in
>   if secretsignals an == [] then ""
>   else
>     "  -- System for secrecy checking\n\n"++
>     -- show genVars++"\n"++ show range++"\n"++
>     "  SYSTEM_S = \n"++
>     declareRenamedTypes renameTypes++ -- Specs2.lhs
>     "    SYSTEM\n"++
>     "      [[" ++
>     format 8 ", " (map (createSecretRenaming1 an) (secretsignals an)) ++
>     allGens ++ hideString
>     ++
>     "  SYSTEM_S_SEQ =\n"++
>     declareRenamedTypes renameTypes++
>     "    SYSTEM\n"++
>     "      [[" ++
>     format 8 ", " (map (createSeqSecretRenaming1 an) (secretsignals an)) ++
>     allGens ++ hideString
>
>   where  getId (s,r) = case (s,r) of
>                       (Agent a, Environment) -> [a]
>                       (Environment, Agent b) -> [b]
>                       (Agent a, Agent b) -> [a,b]

>  -- \\ {| env, send, receive"++
>  --         (ifFlagString an TimeUsed ", tock")++
>  --         (maybeString (directC /= Some [] && authC /= All) ", comm")++
>  --         (ifFlagString an GuessablesUsed 
>  --            ", INTRUDER_M::guess, INTRUDER_M::verify")++
>  --         (ifFlagString an CrackablesUsed ", close")++" |}\n\n"
>        --maybeString
>        --  (hasFlag an UnboundedParallel && messageSpaceMembership /= []) 
>        --  (",\n        " ++ format 8 ", " messageSpaceMembership) ++
>           --maybeString 
>            -- (hasFlag an UnboundedParallel && messageSpaceMembership /= []) 
>            -- (",\n" ++ format 8 ", " messageSpaceMembership) ++

Create single renaming for parallel secrecy spec.  Rename message number nr to 
signal.Claim_Secret.id.sec.ls

>createSecretRenaming1 :: Annotated -> SecretSignal -> Output
>createSecretRenaming1 an (nr,id,sec,ls) =
>   let 
>       (s1,r1,m1,se1,re1) = -- the message in question
>           hd[(s,r,m,se1,re1) | (_,n,s,r,m,_,se1,re1) <- protdesc an, n==nr]
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sigMes = -- message to be renamed
>           if s1==Environment then                               -- Env -> id
>               "env."++id++".(Env"++ nr ++ ", " ++"ALGEBRA_M::applyRenaming("++
>                   showMsg an (receiverMsg m1)++")" ++ 
>               ", <" ++ commaConcat re1 ++ ">)\n"
>           else if r1==Environment then                           -- id -> Env
>               "env."++id++".(Env"++ nr ++ ", " ++ 
>	            "ALGEBRA_M::applyRenaming("++showSenderMsg an m1++")" ++ 
>               ", <" ++ commaConcat se1 ++ ">)\n"
>           else if s1==Agent id then                              -- id -> r1
>               "send."++id++"."++convert r1++sessString++".ALGEBRA_M::rmb((Msg"++nr++", "++ 
>	            showSenderMsg an m1 ++", <"++commaConcat se1++">))\n"
>           else                                              -- s1 -> id
>               "receive."++convert s1++"."++id++sessString++".ALGEBRA_M::rmb((Msg"++nr++
>	            ", "++showMsg an (receiverMsg m1)++", <"++
>	            commaConcat re1++">))\n"
>  in sigMes++"          <- signal.Claim_Secret."++id++
>     ".ALGEBRA_M::applyRenaming("++showMsg an (varMsg sec)++")."++"{"++
>     commaConcat (ls \\ (case sec of Atom a -> [a]; _ -> [])) ++ "}"

Create single renaming for sequential secrecy spec

>createSeqSecretRenaming1 :: Annotated -> SecretSignal -> Output
>createSeqSecretRenaming1 an (nr,id,sec,ls) =
>   let
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       (s1,r1,m1,se1,re1) = -- the message in question
>           hd[(s,r,m,se1,re1) | (_,n,s,r,m,_,se1,re1) <- protdesc an, n==nr]
>       sigMes = -- message to be renamed
>           if s1==Environment then                               -- Env -> id
>               "env."++id++".(Env"++nr++", "++
>               "ALGEBRA_M::applyRenaming("++
>               showMsg an (receiverMsg m1)++")"++
>               ", <"++commaConcat re1 ++ ">)\n"
>           else if r1==Environment then                           -- id -> Env
>               "env."++id++".(Env"++ nr ++ ", " ++  
>               "ALGEBRA_M::applyRenaming("++showSenderMsg an m1++")"  ++ 
>               ", <" ++ commaConcat se1 ++ ">)\n"
>           else if s1==Agent id then                               -- id -> r1
>               "send."++id++"."++convert r1++sessString++".ALGEBRA_M::rmb((Msg"++nr++", "++ 
>               showSenderMsg an m1 ++", <"++
>               commaConcat se1++">))\n"
>           else                                                 -- s1 -> id
>               "receive."++convert s1++"."++id++sessString++
>               ".ALGEBRA_M::rmb((Msg"++nr++", "++ 
>	            showMsg an (receiverMsg m1)++", <"++
>               commaConcat re1++">))\n"
>   in 
>       sigMes ++ "          <- scs.ALGEBRA_M::applyRenaming("++
>       showMsg an (varMsg sec)++").isIntIn({"++
>       commaConcat (id:ls \\ (case sec of Atom a -> [a]; _ -> [])) ++ "})"

>messageSetReduction :: Annotated -> SecretSignal -> Output
>messageSetReduction an (nr,id,sec,ls) =
>   let 
>       (s1,r1,m1,se1,re1) = -- the message in question
>           hd[(s,r,m,se1,re1) | (_,n,s,r,m,_,se1,re1) <- protdesc an, n==nr]
>   in 
>       if s1==Environment then                               -- Env -> id
>           "member(ALGEBRA_M::rmb((Env"++nr++", "++ showMsg an (receiverMsg m1)++
>               ", <"++commaConcat re1 ++ ">)),SYSTEM_M::ENV_MSG" ++ nr ++ ")"
>       else if r1==Environment then                           -- id -> Env
>           "member(ALGEBRA_M::rmb((Env"++ nr ++ ", " ++ showSenderMsg an m1++
>              ", <" ++ commaConcat se1 ++ ">)),SYSTEM_M::ENV_MSG" ++ nr ++ ")"
>       else if s1==Agent id then                               -- id -> r1
>           "member(ALGEBRA_M::rmb((Msg"++nr++", "++ showSenderMsg an m1 ++
>              ", <" ++ commaConcat se1++">)),SYSTEM_M::OUTPUT_MSG" ++ nr ++ ")"
>       else                                                 -- s1 -> id
>           "member(ALGEBRA_M::rmb((Msg"++nr++ ", "++ showMsg an (receiverMsg m1)++
>               ", <"++ commaConcat re1++">)),SYSTEM_M::INPUT_MSG" ++ nr ++ ")"

======================================================================

Make alphabet for secrecy spec

>makeAlpha :: Annotated -> Output
>makeAlpha an =
>  "  Alpha_SECRETS =\n" ++
>  "    Union({\n"++
>  "      {|leak, signal.Claim_Secret.A_ | A_ <- HONEST|}"++
>  ifFlagString an CrackablesUsed ",\n      {|crack|}"++
>  "\n    })\n\n"
>  ++
>  "  Alpha_SEQ_SECRETS = \n" ++
>  "    Union({\n"++
>  "      {|leak, scs|}"++
>  ifFlagString an CrackablesUsed ",\n      {|crack|}"++
>  "\n    })\n\n"
