
>module Intruder(produceIntruder, produceIntruderExports) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import Annotated
>import SecureChannels
>import UnboundParallel

=================================================

>produceIntruder :: Annotated -> Output
>produceIntruder an = 
>  let
>	-- use allSpypicks to derive set of spypicks to be chased.
>	-- allSpypicks = makeOrdering fvts accumList diGenerations
>  in
>  ifFlagString an GuessablesUsed (
>     "  -- Guessable values\n\n"++
>     "  Guessable0 = "++makeUnion 4 (guessables an)++
>     "  Guessable = diff(Guessable0, IK1)\n\n"
>  )++
>  ifFlagString an UnboundedParallel (
>    "  -- Unbound Parallel functions and sets, necessary for deductions\n\n"++
>    "  honest(x) = x != " ++ intruderId an ++ "\n\n"
>  ) ++
>  -- Generate deductions
>  genDeductions an ++ 
>  closeFacts an++
>  ifFlagString an GuessablesUsed makeUndoes++
>  "  -- The intruder\n\n" ++
>  "  -- * leak is used to signal that a possible secret has been learnt\n"++
>  "  -- * hear and say are used to represent hearing or saying a message\n"++
>  "  -- * infer(f,fs) represent deducing fact f from the set of facts fs\n\n"++
>  intruderDef an

=================================================
Deductions

>genDeductions :: Annotated -> Output
>genDeductions an = 
>   let
>       Annotated {
>           newchannels = newchans
>       } = an
>       dtCons = [cons | (_,pats,_) <- dtdefs an, (cons,_:_) <- pats]
>       fns = [f | Atom f <- intruderInitKnows an, isFn (fnts an) f]++dtCons
>   in
>  "  -- Intruder's deductions\n\n" ++
>  "  unSq_ (Sq.ms_) = set(ms_)\n" ++
>  "  unSq_ (m_) = {m_}\n\n" ++
>  "  unknown_(S_) = diff(S_, IK0)\n\n" 
>  ++
>  -- FIXME: the following ought to be in the "exports" section
>  "  Base_Deductions_ =\n" ++
>  "    Union({SqDeductions, UnSqDeductions, \n"++
>  "           EncryptionDeductions, DecryptionDeductions,\n" ++
>  "           VernEncDeductions, VernDecDeductions, \n" ++
>  "           FnAppDeductions, HashDeductions"++
>  ifFlagString an UnboundedParallel (
>    ",\n           SentDeductions, All_Internal_Deductions") ++
>  -- don't allow user deductions with guessables, because we can't undo them
>  (ifNotFlagString an GuessablesUsed ", UserDeductions")++
>  maybeString (inUse ["C","NR-"] newchans) ", SentToDeductions" ++
>  maybeString (inUse ["NF","NRA-"] newchans) ", SentByDeductions" ++
>  maybeString (not (newchans == [])) ", SentByToDeductions, SentByToCDeductions" ++
>  "})\n\n"++
>  (if newchans == [] then "" else
>    (if inUse ["C","NR-"] newchans then
>       (if sessinfo an /= [] then
>         "  SentToDeductions = {(SentTo.(a_, c_, m_), {SentTo.(a_, c_, m_)}) | SentTo.(a_, c_, m_) <- Fact_1}\n\n"
>       else
>         "  SentToDeductions = {(SentTo.(a_, m_), {SentTo.(a_, m_)}) | SentTo.(a_, m_) <- Fact_1}\n\n"
>       )
>     else "") ++
>    (if inUse ["NF","NRA-"] newchans then
>     "  SentByDeductions = Union({\n" ++
>     (if sessinfo an /= [] then
>       "    {(SentBy.(a_, c_, m_), {SentBy.(a_, c_, m_)}) | SentBy.(a_, c_, m_) <- Fact_1}, \n" ++
>       "    {(m_, {SentBy.(a_, c_, m_)}) | SentBy.(a_, c_, m_) <- Fact_1} \n"
>     else
>       "    {(SentBy.(a_, m_), {SentBy.(a_, m_)}) | SentBy.(a_, m_) <- Fact_1}, \n" ++
>       "    {(m_, {SentBy.(a_, m_)}) | SentBy.(a_, m_) <- Fact_1} \n"
>     )++
>     "  })\n\n"
>     else "") ++
>    (if newchans == [] then "" else
>     "  SentByToDeductions = Union({\n" ++
>     (if sessinfo an /= [] then
>       "    {(SentByTo.(a_, b_, c_, m_), {SentByTo.(a_, b_, c_, m_)}) | SentByTo.(a_, b_, c_, m_) <- Fact_1}, \n" ++
>       "    {(m_, {SentByTo.(a_, b_, c_, m_)}) | SentByTo.(a_, b_, c_, m_) <- Fact_1} \n"
>     else
>       "    {(SentByTo.(a_, b_, m_), {SentByTo.(a_, b_, m_)}) | SentByTo.(a_, b_, m_) <- Fact_1}, \n" ++
>       "    {(m_, {SentByTo.(a_, b_, m_)}) | SentByTo.(a_, b_, m_) <- Fact_1} \n"
>     )++
>     "  })\n\n" ++
>     "  SentByToCDeductions = Union({\n" ++
>     (if sessinfo an /= [] then
>       "    {(SentByToC.(a_, b_, c_, m_), {SentByToC.(a_, b_, c_, m_)}) | SentByToC.(a_, b_, c_, m_) <- Fact_1}" 
>     else
>       "    {(SentByToC.(a_, b_, m_), {SentByToC.(a_, b_, m_)}) | SentByToC.(a_, b_, m_) <- Fact_1}" 
>     )++
>     "  })\n\n"
>    )
>  )++
>  (if hasFlag an GuessablesUsed
>   then
>     "  SqDeductions =\n" ++
>     "    {(Sq.fs_, SeqD, set(fs_)) | Sq.fs_ <- Fact_1}\n\n" 
>     ++
>     "  UnSqDeductions =\n" ++
>     "    {(nth(fs_,i_), UnSeq.i_, {Sq.fs_}) | \n"++
>     "       Sq.fs_ <- Fact_1, i_ <- {1..#fs_}}\n\n" 
>     ++
>     "  EncryptionDeductions =\n" ++
>     "    {(Encrypt.(k_,fs_), Enc, union({k_}, set(fs_))) | \n" ++
>     "        Encrypt.(k_,fs_) <- Fact_1}\n\n" 
>     ++
>     "  DecryptionDeductions =\n"++
>     "    {(nth(fs_,i_), Dec.i_, {Encrypt.(k_,fs_), inverse(k_)}) |\n"++
>     "        Encrypt.(k_,fs_) <- Fact_1, k_!=Garbage, i_ <- {1..#fs_}}\n\n"
>     ++
>     "  VernEncDeductions =\n" ++
>     "    {(Xor.(m1_,m2_), VernEnc, union(unSq_(m1_), unSq_(m2_))) | \n" ++
>     "        Xor.(m1_,m2_) <- Fact_1}\n\n" 
>     ++
>     "  VernDecDeductions =\n" ++
>     "      {(m11_, VernDec, union(unSq_(m2_), {Xor.(m1_,m2_)})) | \n" ++
>     "         Xor.(m1_,m2_) <- Fact_1, m11_ <- unSq_(m1_)}\n\n" 
>     ++ 
>     "  HashDeductions = "++
>     "  {(Hash.(f_, ms_), HashD, set(ms_)) | Hash.(f_, ms_) <- Fact_1}\n\n"
>   else
>     "  SqDeductions =\n" ++
>     "    {(Sq.fs_, unknown_(set(fs_))) | Sq.fs_ <- Fact_1}\n\n" 
>     ++
>     "  UnSqDeductions =\n" ++
>     "    {(f_, unknown_({Sq.fs_})) | Sq.fs_ <- Fact_1, f_ <- unknown_(set(fs_))}\n\n" 
>     ++
>     "  EncryptionDeductions =\n" ++
>     "    {(Encrypt.(k_,fs_), unknown_(union({k_}, set(fs_)))) | \n" ++
>     "        Encrypt.(k_,fs_) <- Fact_1}\n\n" 
>     ++
>     "  DecryptionDeductions =\n"++
>     "    {(f_, unknown_({Encrypt.(k_,fs_), inverse(k_)})) |\n" ++
>     "        Encrypt.(k_,fs_) <- Fact_1, f_ <- unknown_(set(fs_))}\n\n"
>     ++
>     "  VernEncDeductions =\n" ++
>     "    {(Xor.(m1_,m2_), unknown_(union(unSq_(m1_), unSq_(m2_)))) | \n" ++
>     "        Xor.(m1_,m2_) <- Fact_1}\n\n" 
>     ++
>     "  VernDecDeductions =\n" ++
>     "      {(m11_, union(unknown_(unSq_(m2_)), {Xor.(m1_,m2_)})) | \n" ++
>     "         Xor.(m1_,m2_) <- Fact_1, m11_ <- unSq_(m1_)}\n\n" 
>     ++ 
>     "  HashDeductions = "++
>     "{(Hash.(f_, ms_), set(ms_)) | Hash.(f_, ms_) <- Fact_1}\n\n"
>     ++
>     (ifFlagString an UnboundedParallel 
>        ("  -- Unbound Parallel Deductions\n\n"
>        ++
>        "  SentDeductions = {(m_, {Sent.(m_,fs_)}) | Sent.(m_,fs_) <- Fact_1}\n\n"
>        ++
>        makeSentDeductions an++ "\n\n")
>     )
>     ++
>     "  UserDeductions = " ++ 
>     makeUnion 4 (map (make_ud an) (deductions an)) ++ "\n"
>  ) 
>  ++ -- end of "if guessablesUsed ..."
>  "  FnAppDeductions = " ++ 
>  makeUnion 4 (map (makeFnAppDed an) fns) ++ "\n"

Display a user deduction

>make_ud :: Annotated -> Deduction -> String
>make_ud an (qs, ms, m) = 
>  "{(" ++ showMsg an m ++ ", {" ++ 
>  commaConcat (map (showMsg an) ms) ++ "}) | " ++
>  commaConcat (map showquant qs) ++ "}"

>showquant (v,t) = v++" <- "++(if t=="TimeStamp" then "TS" else t)

>makeFnAppDed an f = 
>  let ats = findFnDomType (fnts an) f
>      arity = length ats
>      args = ["arg_"++show n++"_" | n <- [1..arity]]
>      appString = f++"("++commaConcat args++")"
>      appSymString = 
>        funname f++"."++
>        (if arity==1 then hd args else "("++commaConcat args++")")
>  in
>  case findFnType1 (fnts an) f of
>    Symb _ _ -> 
>      "{("++appSymString++ifFlagString an GuessablesUsed ", FnApp"++
>      ", unknown_({"++commaConcat args++"})) |\n"++
>      "        "++appSymString++" <- Fact_1}"
>    Defed _ _  ->
>      "{("++appString++ifFlagString an GuessablesUsed ", FnApp"++
>      ", unknown_({"++commaConcat args++"})) |\n"++
>      "        "++commaConcat[arg++" <- "++at | (arg,at) <- zip args ats]++
>      ", member("++appString++", Fact_1)}"
>    _ -> error "makeFnAppDed"

=============================================================================
Close up initial knowledge under deductions; calculate which facts can't 
possibly be learnt by the intruder; reduce deductions appropriately

>closeFacts :: Annotated -> Output
>closeFacts an = 
>  "  -- close up intruder's initial knowledge under deductions;\n"++
>  "  -- calculate which facts cannot be learnt\n\n"++
>  "  components_(Sq.ms_) = \n"++
>  "    if member(Sq.ms_, Fact_1) then {Sq.ms_} else set(ms_)\n"++
>  "  components_(m_) = {m_}\n\n"++
>  "  Seeable_ = \n"++
>  "    Union({unknown_(components_(m_)) | (_,m_,_,_) <- SYSTEM_M::INT_MSG_INFO})\n\n" ++
>  (if hasFlag an GuessablesUsed then
>    "  Close_(IK_, ded_, fact_) =\n" ++
>    "    let IK1_ = \n" ++
>    "          union(IK_, {f_ | (f_,l_,fs_) <- ded_, fs_ <= IK_})\n" ++
>    "        ded1_ = \n"++
>    "          {(f_,l_,fs_) | (f_,l_,fs_) <- ded_, fs_ <= fact_}\n" ++
>    "        fact1_ = Union({IK_, {f_ | (f_,l_,fs_) <- ded_},\n"++
>    "                       Seeable_, Guessable0})\n" ++
>    "    within\n" ++
>    "    if card(IK_)==card(IK1_) and card(ded_)==card(ded1_)\n"++
>    "       and card(fact_)==card(fact1_)\n" ++
>    "    then (IK_, {(f_,l_,fs_) | (f_,l_,fs_) <- ded_, not(fs_ <= IK_)}, fact_)\n" ++
>    "    else Close_(IK1_, ded1_, fact1_)\n\n" 
>  else "")
>  ++
>  maybeString (not (hasFlag an UnboundedParallel)) (
>     "  (IK1, Deductions_, KnowableFact_) = \n"++ 
>     "    Close_(ALGEBRA_M::applyRenamingToSet(IK0), \n"++
>     "           ALGEBRA_M::applyRenamingToDeductions(Base_Deductions), \n"++
>     "           ALGEBRA_M::applyRenamingToSet(Fact_1))\n\n"
>   )
>  ++
>  ifNotFlagString an UnboundedParallel "  LearnableFact = diff(KnowableFact, IK1)\n\n" 

KnowableFact is the set of facts that the intruder could possibly learn.  IK1
is the intruder's initial knowledge.  Deductions is the set of deductions of
the form (f,fs) where f in KnowableFact\IK1, fs <= KnowableFact\IK1.

===============================================
make definition of undoes

>makeUndoes :: Output
>makeUndoes =
>  "  -- Undoing deductions\n\n"++
>  "  undoes(Encrypt.(k_,fs_), Enc, f1s_) = \n"++
>  "    {ded | ded@@(f_, Dec.i_, ffs_) <- Deductions, \n"++
>  "           ffs_ == {Encrypt.(k_,fs_), inverse(k_)}} \n"
>  ++
>  "  undoes(f_, Dec.i_, f1s_) = \n"++
>  "    {ded | ded@@(Encrypt.(k_,fs_), Enc, ffs_) <- Deductions, \n"++ 
>  "           f1s_ == {Encrypt.(k_,fs_), inverse(k_)}} \n"
>  ++
>  "  undoes(Sq.fs_, SeqD, f1s_) =\n"++
>  "    {ded | ded@@(f_, UnSeq.i, ffs_) <- Deductions, \n"++
>  "           ffs_ == {Sq.fs_}}\n"
>  ++
>  "  undoes(f_, UnSeq.i, f1s_) = \n"++
>  "    {ded | ded@@(fs_, Seq.i_, ffs_) <- Deductions, \n"++ 
>  "           f1s_ == {fs_}} \n"
>  ++
>  "  undoes(Xor.(m1_,m2_), VernEnc, f1s_) =\n"++
>  "    {ded | ded@@(f_, VernDec, ffs_) <- Deductions, \n"++ 
>  "           ffs_ == {Xor.(m1_,m2_),m1_} or ffs_ == {Xor.(m1_,m2_),m2_}} \n" 
>  ++
>  "  undoes(f_, VernDec, f1s_) =\n"++
>  "    union(\n"++
>  "      {ded | ded@@(Xor.(m1_,m2_), VernEnc, ffs_) <- Deductions, \n"++ 
>  "             f1s_=={Xor.(m1_,m2_),m1_} or f1s_=={Xor.(m1_,m2_),m2_}},\n"++
>  "      {ded | ded@@(f1_, VernDec, ffs_) <- Deductions,\n"++
>  "             f_!=f1_, union({f_},f1s_)==union({f1_},ffs_)}\n"++
>  "    )\n"
>  ++
>  "  undoes(_,FnApp,_) = {}\n"
>  ++
>  "  undoes(_,HashD,_) = {}\n\n"


===============================================
Definition of intruder

>intruderDef :: Annotated -> Output
>intruderDef an =
>  let	
>       Annotated {
>           channels = (secC,authC,directC),
>           newchannels = newchans,
>           intruderId = intruderName,
>           protdesc = protdes
>       } = an
>       knows = if hasFlag an GuessablesUsed || hasFlag an TimestampsUsed then 
>               "KNOWS(f_,ms_,fss_,ds_)" else "KNOWS(f_,ms_,ds_)"
>       sessString = if sessinfo an /= [] then ".c_" else ""
>       sessString' = if sessinfo an /= [] then ", c_ <- SessionIds" else ""
>       sessStringI = if sessinfo an /= [] then ", c_ <- {c_" ++ [head intruderName] ++ "}" else ""
>       sessString'' = if sessinfo an /= [] then ",c_" else ""
>  in
>   "  -- Component of intruder for currently unknown fact f_:\n"++
>   "  -- * ms_ is the set of messages that contain f_ at the top level\n"++
>   "  -- * fss_ is the set of sets of facts from which f_ can be deduced\n"++
>   "  -- * ds_ is the set of deductions that use f_\n\n"++
>   "  IGNORANT(f_,ms_,fss_,ds_) =\n" ++
>   "    hear?m_:ms_ -> " ++ knows ++"\n" ++
>   "    []\n" ++
>   (if hasFlag an GuessablesUsed then
>     "    ([] (l_, fs_) : fss_, not(member(f_,fs_)) @ \n"++
>     "        infer.(f_,l_,fs_) -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    (member(f_,Guessable) & guess.f_ -> KNOWS''(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    guess?g_:diff(Guessable,{f_}) -> IGNORANT'(f_,ms_,fss_,ds_)\n"
>   else 
>     "    ([] fs_ : fss_, not(member(f_,fs_)) @ \n"++
>     "        infer.(f_,fs_) -> " ++ knows ++ ")\n"
>   )
>   ++ifFlagString an TimestampsUsed(
>   "    [] tock -> (IGNORANT(f_,ms_,fss_,ds_)\n"++
>   "      -- We can only be the updated version if there is a fact that can\n"++
>   "      -- be updated to us.\n"++
>   "      [] card({f1_ | f1_ <- UpdateableFacts, updt(f1_) == f_, f_ != f1_}) > 0 &\n"++
>   "          tockInfer.f_ -> "++knows++")\n"
>   )
>   ++
>   ifFlagString an CrackablesUsed (
>     "    []\n" ++
>     "    member(f_, ALL_CRACKABLES) & crack.f_ -> "++knows++"\n"
>   )++
>   "\n" ++ 
>   ifFlagString an GuessablesUsed
>    ("  -- Component for currently unknown fact f_, after a guess\n\n"++
>     "  IGNORANT'(f_,ms_,fss_,ds_) = \n"++
>     "    ([] (l_,fs_) : fss_, not(member(f_,fs_)) @\n"++
>     "      infer.(f_,l_,fs_) -> \n"++
>     "      if member(f_,ASYMMETRIC_KEYS) and member(inverse(f_), KnowableFact)\n"++
>     "      then ([] g_ : Guessable @ \n"++
>     "              verify.(f_,g_) -> vsync.g_ -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "           []\n"++
>     "           notVerify.f_ -> KNOWS'(f_,ms_,fss_,ds_)\n"++
>     "      else KNOWS'(f_,ms_,fss_,ds_)\n"++
>     "    )\n"++
>     "    []\n"++
>     "    vsync?g_:diff(Guessable,{f_}) -> IGNORANT(f_,ms_,fss_,ds_)\n"
>     ++"\n"
>   )
>   ++
>   "  -- Component of intruder for known fact f_\n\n"++
>   "  "++knows ++ " =\n" ++
>   "    hear?m_:ms_ -> "++ knows ++ "\n" ++
>   "    []\n" ++
>   "    say?m_:ms_ -> " ++ knows ++ "\n" ++
>   "    [] \n" ++
>   "    ([] ded@@(f1_,"++(ifFlagString an GuessablesUsed "l_,")++"fs_) : ds_, f1_!=f_"
>       ++" @ infer.ded -> " ++ knows ++ ")\n" ++
>   "    []\n" ++
>   "    member(f_,ALL_SECRETS) & leak.f_ -> " ++ knows ++ "\n" ++
>   ifFlagString an TimestampsUsed
>     ("    [] tock ->\n"++
>      "      (if updt(f_) != f_ then\n"++ 
>      "        tockInfer.updt(f_) -> IGNORANT(f_,ms_,fss_,ds_)\n"++
>      "      else -- Allow more infers (consider if we obtain a fresher version of this message)\n"++
>      "        KNOWS(f_,ms_,fss_,ds_)\n"++
>      "        [] tockInfer.f_ -> "++knows++")\n"
>   )
>   ++
>   ifFlagString an GuessablesUsed
>    ("    []\n"++
>     "    -- The following is required because if it is not then a deduction deducing a\n"++
>     "    -- fact we already know may be allowed by the DEDUCTION process during the\n"++
>     "    -- guessing phase which would allow it to be used as a verifier that a\n"++
>     "    -- guess is correct.\n"++ 
>     "    ([] (l_,fs_) : fss_ @ infer.(f_,l_,fs_) -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    guess?g_ -> KNOWS'(f_,ms_,fss_,ds_)\n")
>   ++
>   ifFlagString an CrackablesUsed (
>     "    []\n" ++
>     "    member(f_, ALL_CRACKABLES) & crack.f_ -> "++knows++"\n"
>   )++
>   "\n" ++
>   ifFlagString an GuessablesUsed (
>     "  -- Component for known fact f_ after guess\n\n"++
>     "  KNOWS'(f_,ms_,fss_,ds_) =\n"++
>     "    infer?(f1_,l_,fs_) : ds_ -> KNOWS'(f_,ms_,fss_,ds_)\n"++
>     "    []\n"++
>     "    ([] (l_,fs_) : fss_ @ \n"++
>     "        infer.(f_,l_,fs_) -> [] g_ : Guessable @ verify.(f_,g_) -> \n"++
>     "        vsync.g_ -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    vsync?g_:diff(Guessable,{f_}) -> KNOWS(f_,ms_,fss_,ds_)\n"++
>     "    []\n"++
>     "    member(f_,ASYMMETRIC_KEYS) and member(inverse(f_), KnowableFact) &\n"++
>     "      ([] g_ : Guessable @ \n"++
>     "         verify.(inverse(f_),g_) -> vsync.g_ -> KNOWS(f_,ms_,fss_,ds_))\n\n"++
>     "  -- Component for guessed fact f_\n\n"++
>     "  KNOWS''(f_,ms_,fss_,ds_) =\n"++
>     "    ([] (f1_,l_,fs_) : ds_, f_!=f1_ @\n"++
>     "           infer.(f1_,l_,fs_) -> KNOWS''(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    ([] (l_,fs_) : fss_ @ \n"++
>     "        infer.(f_,l_,fs_) -> verify.(f_,f_) -> \n"++
>     "        vsync!f_ -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    ([] ff_:diff(KnowableFact,{f_}) @ verify.(ff_,f_) -> \n"++
>     "      vsync!f_ -> KNOWS(f_,ms_,fss_,ds_))\n"++
>     "    []\n"++
>     "    vsync?g_:diff(Guessable,{f_}) -> KNOWS(f_,ms_,fss_,ds_)\n"
>     ++"\n")
>   ++
>   "  -- Alphabet of this component\n\n"++
>   "  AlphaL(f_,ms_,fss_,ds_) =\n" ++
>   "    Union({(if member(f_,ALL_SECRETS) then {leak.f_} else {}),\n" ++
>   "           {hear.m_, say.m_ | m_ <- ms_},\n" ++
>   (if hasFlag an GuessablesUsed
>    then
>     "           {infer.(f_,l_,fs_) | (l_,fs_) <- fss_},\n" ++
>     "           {infer.(f1_,l_,fs_) | (f1_,l_,fs_) <- ds_},\n" ++
>     "           {|guess|},\n" ++
>     "           if member(f_,Guessable)\n"++
>     "             then {verify.(ff_,f_) | ff_ <- KnowableFact}\n"++
>     "             else {},\n"++
>     "           {|verify.(f_,f1_) | f1_ <- Guessable|},\n"++
>     "           if member(f_,ASYMMETRIC_KEYS) and member(inverse(f_), KnowableFact)\n"++
>     "             then union({notVerify.f_}, \n"++
>     "                        {verify.(inverse(f_),f1_) | f1_ <- Guessable})\n"++
>     "             else {},\n"++
>     "           {|vsync|}"
>    else
>     "           {infer.(f_,fs_) | fs_ <- fss_},\n" ++
>     "           {infer.(f1_,fs_) | (f1_,fs_) <- ds_}") 
>   ++
>   ifFlagString an CrackablesUsed 
>     ",\n           if member(f_, ALL_CRACKABLES) then {crack.f_} else {}"
>   ++
>   ifFlagString an TimestampsUsed 
>     ",\n           {tock, tockInfer.f_, tockInfer.updt(f_)}"
>   ++
>   "\n         })\n\n" ++
>   "  -- Set of all (f_, ms_, fss_, ds_) for which intruder components \n"++
>   "  -- must be built\n\n"++
>   "  f_ms_fss_ds_s"++(ifNotFlagString an GuessablesUsed "(Deductions,LearnableFact)")++ " = \n" ++
>   "    let rid_ = relational_image"++
>   (if hasFlag an GuessablesUsed
>    then "({(f_,(l_,fs_)) | (f_,l_,fs_) <- Deductions})\n"
>    else "(Deductions)\n")
>   ++
>   "        msf_ = relational_image({(f_, m_) | m_ <- MSG_BODY, f_ <- unSq_(m_)})\n" ++
>   "        xsf_ = relational_image({(f_, x_) | x_@@(_,"++
>   ifFlagString an GuessablesUsed "l_,"++"fs_) <- Deductions,\n"++
>   "                                            f_ <- fs_})\n" ++
>   "    within {(f_, msf_(f_), rid_(f_), xsf_(f_)) | f_ <- "++
>   (if hasFlag an GuessablesUsed then "KnowableFact" else "LearnableFact")++
>   "}\n\n" ++
>   ifFlagString an GuessablesUsed
>    ("  -- Processes to control deductions\n\n"++
>     "  DEDUCTION(f_,l_,fs_) =\n"++
>     "    infer.(f_,l_,fs_) -> "++(
>          if hasFlag an TimestampsUsed then 
>              "tock -> DEDUCTION(f_,l_,fs_)\n"++
>              "[] tock -> DEDUCTION(f_,l_,fs_)\n"
>          else "STOP\n")++
>     "    []\n"++
>     "    [] (fa_,la_,fsa_) : undoes(f_,l_,fs_) @\n"++
>     "         infer.(fa_,la_,fsa_) -> DEDUCTION(f_,l_,fs_)\n\n"++
>     "  alphaDEDUCTION(f_,l_,fs_) =\n"++
>     "    Union({{infer.(f_,l_,fs_)}, \n"++
>     "          {infer.(fa_,la_,fsa_) | (fa_,la_,fsa_) <- undoes(f_,l_,fs_)}"++
>     (ifFlagString an TimestampsUsed ",\n          { tock }\n")++
>     "         })\n\n")
>   ++
>   (ifFlagString an GuessablesUsed "  -- Put components together in parallel ...\n\n")++
>   (if hasFlag an GuessablesUsed
>    then
>     "  INTRUDER_00 = \n" ++
>     "    (|| (f_,ms_,fss_,ds_) : f_ms_fss_ds_s @ \n" ++
>     "         [AlphaL(f_,ms_,fss_,ds_)]\n"++
>     "           if member(f_,IK1) then KNOWS(f_,ms_,fss_,ds_)\n"++
>     "           else IGNORANT(f_,ms_,fss_,ds_)\n" ++
>     "    )\n"++
>     "    [| {| infer"++(ifFlagString an TimestampsUsed ", tock")++" |} |]\n" ++
>     "    (|| (f_,l_,fs_) : Deductions' @ \n" ++
>     "         [alphaDEDUCTION(f_,l_,fs_)] DEDUCTION(f_,l_,fs_))\n\n"
>    else ""
>   )++
>   "  -- Rename events appropriately\n\n"++
>   "  BUILD_INTRUDER_0(INTRUDER_0) =\n" ++
>   "    ((chase(INTRUDER_0)\n"++
>   (if (newchans == []) then (
>     -- rename hear events on authenticated and secret channels to send
>     (let msgs = 
>            makeUnion' 9
>             ["SYSTEM_M::DIRECT_MSG"++n | 
>               (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>               isIn n authC && isIn n secC]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_"++" <- "++"send.A_."++intruderName++".(l_,m_,se_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}) ]] \n"))++
>     -- rename hear events on authenticated channels and all non-specified channels to send
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               (isIn n authC && not (isIn n secC)) || not (isIn n directC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_"++" <- "++"send.A_.B_.(l_,m_,se_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))++
>     -- rename hear events on secret channels to comm
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n secC && not(isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_"++" <- "++"comm.A_."++intruderName++".(l_,m_,se_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}) ]] \n"))++
>     -- rename hear events on direct channels to send/comm
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n directC && not (isIn n secC || isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_ <- send.A_.B_.(l_,m_,se_), \n"++
>      "         hear.m_ <- comm.A_.B_.(l_,m_,se_,re_) | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))
>   ) else (
>     -- C ^ NR-
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _, Agent _,_,_,_,_) <- protdes,
>                                 channelIs ["C","NR-"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_ <- send.A_." ++ intruderName ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++ 
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "})" ++ sessString' ++" ]] \n" ++
>      "      [[ hear.SentTo.(B_" ++ sessString'' ++ ",m_) <- hear.SentTo.(B_" ++ sessString'' ++ ",m_), hear.SentTo.(B_" ++ sessString'' ++ ",m_) <- send.A_.B_" ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++ 
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_),{" ++ intruderName ++ "})" ++ sessString' ++" ]] \n")) ++
>     -- NF ^ NRA-
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _, Agent _,_,_,_,_) <- protdes,
>                                 channelIs ["NF","NRA-"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.SentBy.(A_" ++ sessString'' ++ ",m_) <- hear.SentBy.(A_" ++ sessString'' ++ ",m_), hear.SentBy.(A_" ++ sessString'' ++ ",m_) <- send.A_.B_" ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++ 
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "}), \n" ++
>      "         B_ <- ReceiverType(l_)" ++ sessString' ++" ]] \n")) ++
>     -- NF ^ NRA- ^ NR-, NF ^ NRA- ^ NR
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                 channelIs ["NF","NRA-","NR-"] (channelSelect n newchans) ||
>                                 channelIs ["NF","NRA-","NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.SentByTo.(A_,B_" ++ sessString'' ++ ",m_) <- hear.SentByTo.(A_,B_" ++ sessString'' ++ ",m_), \n" ++
>      "         hear.SentByTo.(A_,B_" ++ sessString'' ++ ",m_) <- send.A_.B_" ++ sessString ++ ".(l_,m_,se_) | \n"++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "}), \n" ++
>      "         B_ <- ReceiverType(l_)" ++ sessString' ++" ]] \n")) ++
>     -- C ^ NRA- ^ NR-, C ^ NRA ^ NR-, C ^ NF ^ NRA- ^ NR-, C ^ NF ^ NRA- ^ NR, C ^ NF ^ NRA ^ NR-, C ^ NF ^ NRA ^ NR
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                 channelIs ["C",     "NRA-","NR-"] (channelSelect n newchans) ||
>                                 channelIs ["C",     "NRA", "NR-"] (channelSelect n newchans) ||
>                                 channelIs ["C","NF","NRA-","NR-"] (channelSelect n newchans) ||
>                                 channelIs ["C","NF","NRA-","NR"] (channelSelect n newchans) ||
>                                 channelIs ["C","NF","NRA", "NR-"] (channelSelect n newchans) ||
>                                 channelIs ["C","NF","NRA", "NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- hear.SentByToC.(A_,B_" ++ sessString'' ++ ",m_), \n" ++
>      "         hear.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- send.A_.B_" ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++" ]] \n" ++
>      "      [[ hear.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_) <- hear.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_), \n" ++
>      "         hear.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_) <- send.A_." ++ intruderName ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "})" ++ sessString' ++" ]] \n")) ++
>     -- everything else (i.e. bottom)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                 channelIs [] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ hear.m_ <- hear.m_, hear.m_ <- send.A_.B_" ++ sessString ++ ".(l_,m_,se_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_),{" ++ intruderName ++ "}), \n" ++
>      "         B_ <- ReceiverType(l_)" ++ sessString' ++" ]] \n"))
>   ))
>   ++
>   -- block any remaining hear events
>   "     [|{| hear |}|] STOP)\n"++
>   (if (newchans == []) then (
>     -- rename authenticated say events to receive
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n authC]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.m_ <- say.m_, say.m_"++" <- "++"receive."++intruderName++".B_.(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))++
>     -- rename non authenticated say events to receive
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               not (isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.m_"++" <- "++"receive.A_.B_.(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", \n"++
>      "         A_ <- SenderType(l_), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))
>   ) else (
>     -- send / fake (C ^ NR-, C ^ NRA- ^ NR-, C ^ NRA ^ NR-, _|_)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["C",      "NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NRA", "NR-"] (channelSelect n newchans) ||
>                               channelIs [] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.m_ <- say.m_, say.m_ <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_) | \n"++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- SenderType(l_), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessStringI ++ " ]] \n"))++
>     -- send (NF ^ NRA-, NF ^ NRA- ^ NR-, NF ^ NRA- ^ NR, C ^ NF ^ NRA- ^ NR-, C ^ NF ^ NRA- ^ NR, C ^ NF ^ NRA ^ NR-, C ^ NF ^ NRA ^ NR)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs [    "NF","NRA-"] (channelSelect n newchans) ||
>                               channelIs [    "NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs [    "NF","NRA-","NR"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA-","NR"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA", "NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA", "NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.m_ <- say.m_, say.m_ <- receive." ++ intruderName ++ ".B_" ++ sessString ++ ".(l_,m_,re_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessStringI ++ " ]] \n")) ++
>     -- forward / hijack (C ^ NR-)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["C","NR-"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentTo.(B_" ++ sessString'' ++ ",m_) <- say.SentTo.(B_" ++ sessString'' ++ ",m_), say.SentTo.(B_" ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- SenderType(l_), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n")) ++
>     -- forward / redirect (NF ^ NRA-)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["NF","NRA-"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentBy.(A_" ++ sessString'' ++ ",m_) <- say.SentBy.(A_" ++ sessString'' ++ ",m_), say.SentBy.(A_" ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_) | \n"++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_), {" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n")) ++
>     -- dishonest redirect (C ^ NRA- ^ NR-, NF ^ NRA- ^ NR-, C ^ NRA ^ NR-, C ^ NF ^ NRA- ^ NR-, C ^ NF ^ NRA ^ NR-)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["C",     "NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs [    "NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C",     "NRA", "NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA", "NR-"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_) <- say.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_), \n" ++
>      "         say.SentByTo.(A_," ++ intruderName ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_) | \n"++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n"++
>      "         A_ <- diff(SenderType(l_), {" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n")) ++
>     -- forward / dishonest hijack (C ^ NRA- ^ NR-, C ^ NF ^ NRA- ^ NR-, C ^ NF ^ NRA- ^ NR)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["C",     "NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA-","NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_), \n" ++
>      "         say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_), \n" ++
>      "         say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- receive." ++ intruderName ++ ".B_" ++ sessString ++ ".(l_,m_,re_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n"++
>      "         A_ <- diff(SenderType(l_), {" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n")) ++
>     -- forward / dishonest hijack ()
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG" ++ n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["NF","NRA-","NR-"] (channelSelect n newchans) ||
>                               channelIs ["NF","NRA-","NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentByTo.(A_,B_" ++ sessString'' ++ ",m_) <- say.SentByTo.(A_,B_" ++ sessString'' ++ ",m_), \n" ++ 
>      "         say.SentByTo.(A_,B_" ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_), \n" ++
>      "         say.SentByTo.(A_,B_" ++ sessString'' ++ ",m_) <- receive." ++ intruderName ++ ".B_" ++ sessString ++ ".(l_,m_,re_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_), {" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n")) ++
>     -- forward (C ^ NRA ^ NR-, C ^ NF ^ NRA ^ NR-, C ^ NF ^ NRA ^ NR)
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelIs ["C","NRA","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA","NR-"] (channelSelect n newchans) ||
>                               channelIs ["C","NF","NRA","NR"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_), say.SentByToC.(A_,B_" ++ sessString'' ++ ",m_) <- receive.A_.B_" ++ sessString ++ ".(l_,m_,re_) | \n" ++
>      "         (l_,m_,se_,re_) <- " ++ msgs ++ ", \n" ++
>      "         A_ <- diff(SenderType(l_), {" ++ intruderName ++ "}), \n" ++
>      "         B_ <- diff(ReceiverType(l_), {" ++ intruderName ++ "})" ++ sessString' ++ " ]] \n"))
>   ))
>   ++
>   -- block any remaining send events
>   "     [|{| say |}|] STOP)\n"++
>   "\n" ++
>   "  -- Add in facts that are known initially\n\n"++
>   "  SAY_KNOWN_0"++(ifNotFlagString an GuessablesUsed "(IK1)")++" = \n" ++
>   "    (inter(IK1, ALL_SECRETS) != {} & dummy_leak -> SAY_KNOWN_0"++(ifNotFlagString an GuessablesUsed "(IK1)")++") \n" ++
>   "    [] dummy_send -> SAY_KNOWN_0"++(ifNotFlagString an GuessablesUsed "(IK1)")++" \n" ++
>   "    [] dummy_receive -> SAY_KNOWN_0"++(ifNotFlagString an GuessablesUsed "(IK1)")++" \n\n" ++
>   "  SAY_KNOWN"++(ifNotFlagString an GuessablesUsed "(IK1)")++" =\n" ++
>   "    SAY_KNOWN_0"++(ifNotFlagString an GuessablesUsed "(IK1)")++"\n" ++
>   "      [[ dummy_leak <- leak.f_ | f_ <- inter(IK1, ALL_SECRETS) ]]\n" ++
>   (if (newchans == []) then (
>     -- rename dummy send events on authenticated and secret channels to send
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n authC && isIn n secC]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_send <- dummy_send, dummy_send"++" <- "++"send.A_."++intruderName++".(l_,m_,se_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}) ]] \n"))++
>     -- rename dummy send events on authenticated channels and all non-specified channels to send
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               (isIn n authC && not (isIn n secC)) || not (isIn n directC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_send <- dummy_send, dummy_send"++" <- "++"send.A_.B_.(l_,m_,se_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))++
>     -- rename dummy send events on secret channels to comm
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n secC && not(isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_send <- dummy_send, dummy_send"++" <- "++"comm.A_."++intruderName++".(l_,m_,se_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}) ]] \n"))++
>     -- rename dummy send events on direct channels to send/comm
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n directC && not (isIn n secC || isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_send <- dummy_send, dummy_send"++" <- "++"send.A_.B_.(l_,m_,se_), \n"++
>      "         dummy_send"++" <- "++"comm.A_.B_.(l_,m_,se_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))++
>     -- rename authenticated dummy_receive events to receive
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               isIn n authC]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_receive <- dummy_receive, dummy_receive"++" <- "++"receive."++intruderName++".B_.(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         B_ <- ReceiverType(l_) ]] \n"))++
>     -- rename non authenticated dummy_receive events to receive
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               not (isIn n authC)]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_receive <- dummy_receive, dummy_receive"++" <- "++"receive.A_.B_.(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- SenderType(l_), \n"++
>      "         B_ <- ReceiverType(l_) ]] \n\n"))
>   ) else (
>     -- All channels
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_send <- dummy_send, dummy_send"++" <- "++"send.A_.B_" ++ sessString ++ ".(l_,m_,se_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- diff(SenderType(l_),{"++intruderName++"}), \n"++
>      "         B_ <- ReceiverType(l_)" ++ sessString' ++ " ]] \n"))++
>     -- Fakeable channels
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               not (channelSatisfies ["NF"] (channelSelect n newchans))]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_receive <- dummy_receive, dummy_receive"++" <- "++"receive.A_.B_" ++ sessString ++ ".(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         A_ <- SenderType(l_), \n"++
>      "         B_ <- ReceiverType(l_)" ++ sessStringI ++ " ]] \n"))++
>     -- NF
>     (let msgs = makeUnion' 9 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                               channelSatisfies ["NF"] (channelSelect n newchans)]
>      in maybeString (msgs /= "{}") (
>      "      [[ dummy_receive <- dummy_receive, dummy_receive <- receive." ++ intruderName ++ ".B_" ++ sessString ++ ".(l_,m_,re_)"++" | \n"++
>      "         (l_,m_,se_,re_) <- "++msgs++", components_(m_) <= IK1, \n"++
>      "         B_ <- ReceiverType(l_)" ++ sessStringI ++ " ]] \n\n"))
>   ))
>   ++
>   "  STOP_SET = "++
>   makeUnion 4 (
>     ["{ dummy_send, dummy_receive }"] ++
>     -- Below is not needed as we never rename say to send.I....
>     --["{| send."++intruderName++" |}"] ++
>     (let msgs = makeUnion' 6 ["SYSTEM_M::DIRECT_MSG"++n | (_,n,Agent _,Agent _,_,_,_,_) <- protdes,
>                                isIn n directC && not (isIn n authC || isIn n secC)]
>      in if (msgs /= "{}") then [
>      "{| send.A."++intruderName++".(l_,m_,se_) | "++
>      "(l_,m_,se_,re_) <- "++msgs++", A <- HONEST |}"]
>     else [])
>   )++
>   "\n"
>   where
>	getVars [] = []
>	getVars ((_,vs):ls) = vs:getVars ls
>	makeAllSeqs [] = []
>	makeAllSeqs (ls:xs) =
>	    ("<" ++ commaConcat ls ++ ">"):makeAllSeqs xs

======================================================================

>produceIntruderExports :: Annotated -> Output
>produceIntruderExports an =
>  let
>    isNotFn (Atom a) = not (isFn (fnts an) a)
>    isNotFn _ = True
>    dtAtoms = [Atom cons | (_,pats,_) <- dtdefs an, (cons,[]) <- pats]
>    initKnows' = filter isNotFn (intruderInitKnows an)++dtAtoms
>    iK00string = format 13 ", " 
>                     (map (showMsg an) initKnows' ++ 
>           ["Garbage"])
>    intrudername = "BUILD_INTRUDER_0(INTRUDER_0)"
>  in
>  senderReceiverTypes an
>  ++
>    "  -- Intruder's initial knowledge\n\n"++
>    (if hasFlag an TimestampsUsed
>     then "  IK0 = union({"++iK00string++"}, TimeStamp)\n\n"
>          else "  IK0 = {" ++ iK00string++"}\n\n"
>    ) ++
>    maybeString (not (hasFlag an UnboundedParallel)) 
>      "  Deductions = Deductions_\n\n" ++
>    "  Base_Deductions = Base_Deductions_\n\n"++
>    (if hasFlag an UnboundedParallel then
>      "  All_External_and_Internal_Deductions =  All_External_and_Internal_Deductions_\n\n"++
>      "  Close_(IK_, ded_, fact_) =\n" ++
>      "    CloseButNotFacts_(IK_, ded_, fact_, { })\n\n"++
>       
>      "  -- The method below is used to calculate IK1 and Deductions and is important\n"++
>      "  -- when authentication checks are being done. If no check was done on f being\n"++
>      "  -- in Facts then the infer event corresponding to a signal may be hidden.\n"++
>      "  CloseButNotFacts_(IK_, ded_, fact_, signal_facts_) =\n" ++
>      "    let IK1_ = \n" ++
>      "          union(IK_, {f_ | (f_,fs_) <- ded_, fs_ <= IK_ and not member(f_, signal_facts_)})\n" ++
>      "        ded1_ = \n"++
>      "          {(f_,fs_) | (f_,fs_) <- ded_, not (member(f_,IK_)),\n"++
>      "                      fs_ <= fact_}\n" ++
>      "    within\n" ++
>      "    if card(IK_)==card(IK1_) and card(ded_)==card(ded1_)\n"++
>      "    then (IK_, {(f_,diff(fs_,IK_)) | (f_,fs_) <- ded_})\n" ++
>      "    else CloseButNotFacts_(IK1_, ded1_, fact_, signal_facts_)\n\n"++
>      "  -- Calculate knowable facts based using the external and internal deductions\n"++
>      "  (KnowableFact_, _) = \n"++ 
>      "    Close_(ALGEBRA_M::applyRenamingToSet(IK0), \n"++
>      "           ALGEBRA_M::applyRenamingToDeductions(All_Deductions), \n"++
>      "           ALGEBRA_M::applyRenamingToSet(Fact_1))\n\n"
>    else if not (hasFlag an GuessablesUsed) then
>      "  Close_(IK_, ded_, fact_) =\n" ++
>      "    CloseButNotFacts_(IK_, ded_, fact_, { })\n\n"++
>      "  -- The method below is used to calculate IK1 and Deductions and is important\n"++
>      "  -- when temporal checks are being done. If no check was done on f being\n"++
>      "  -- in Facts then the infer event corresponding to a intruder send event may be hidden.\n"++
>      "  CloseButNotFacts_(IK_, ded_, fact_, excludedFacts_) =\n" ++
>      "    let IK1_ = \n" ++
>      "          union(IK_, {f_ | (f_,fs_) <- ded_, fs_ <= IK_ and not member(f_,excludedFacts_)})\n" ++
>      "        ded1_ = \n"++
>      "          {(f_,fs_) | (f_,fs_) <- ded_, not (member(f_,IK_)),\n"++
>      "                      fs_ <= fact_}\n" ++
>      "        fact1_ = Union({IK_, {f_ | (f_,fs_) <- ded_}, Seeable_})\n" ++
>      "    within\n" ++
>      "    if card(IK_)==card(IK1_) and card(ded_)==card(ded1_)\n"++
>      "       and card(fact_)==card(fact1_)\n" ++
>      "    then (IK_, {(f_,diff(fs_,IK_)) | (f_,fs_) <- ded_}, fact_)\n" ++
>      "    else Close_(IK1_, ded1_, fact1_)\n\n"        
>    else "")
>    ++
>    "KnowableFact = KnowableFact_ \n" ++
>    (ifNotFlagString an GuessablesUsed (
>    "  -- Put components together in parallel\n"++
>    "  INTRUDER_00(Deductions,LearnableFact) = \n" ++
>    "    (|| (f_,ms_,fss_,ds_) : f_ms_fss_ds_s(Deductions,LearnableFact) @ \n" ++
>    "         [AlphaL(f_,ms_,fss_,ds_)] IGNORANT(f_,ms_,fss_,ds_))\n\n")
>    )++
>    ifNotFlagString an UnboundedParallel ("  INTRUDER_0"++ 
>    " = INTRUDER_00"++(ifNotFlagString an GuessablesUsed "(Deductions, LearnableFact)")++" \\ {|infer" 
>    ++
>    (ifFlagString an GuessablesUsed ", vsync") ++
>    (ifFlagString an TimestampsUsed ", tockInfer")++
>    "|}\n\n")
>    ++
>    "  -- Set of all deductions that could occur\n"++
>    "  COMBINED_DEDUCTIONS =\n"++
>    "    let ds_ = "++makeUnion 8 (
>         if hasFlag an UnboundedParallel then 
>           ["AUTH"++show n++"_M::RenamedDeductions" | n <- [1..length (auths an)]]++
>           (if secrets an /= [] then ["SECRET_M::Deductions"] else [])++
>           ["TEMPORAL_SPEC_"++show n++"_M::Deductions" | n <- [1..length (temporalSpecs an)]]
>         else ["INTRUDER_M::Deductions"])++
>    "    within -- Don't you hate hacks like this (FDR does not allow empty channel types)?\n"++
>    "      if ds_ == {} then {(Garbage, "++
>    ifFlagString an GuessablesUsed "HashD, "++"{Garbage})} else ds_\n\n"++
>    "  -- Declare channels:\n"++
>    "  channel hear, say : MSG_BODY\n"++
>    "  channel dummy_leak, dummy_send, dummy_receive\n"++
>    ifFlagString an GuessablesUsed
>     ("  datatype DedLabel = Enc | Dec.Int | SeqD | UnSeq.Int | \n"++
>      "                      VernEnc | VernDec | HashD | FnApp \n\n"++
>      "  channel guess : Guessable\n"++
>      "  channel verify : (KnowableFact,Guessable)\n"++
>      "  channel vsync : Guessable\n"++
>      "  channel notVerify : ASYMMETRIC_KEYS\n") ++
>    ifFlagString an TimestampsUsed (
>    "  UpdateableFacts = union({f_ | (f_,"++(ifFlagString an GuessablesUsed "l_,")
>       ++"fs_) <- COMBINED_DEDUCTIONS},KnowableFact)\n"++
>    "  channel tockInfer : UpdateableFacts\n"
>    )++
>    "\n"++
>    "  -- Complete intruder\n\n"++(
>    if hasFlag an GuessablesUsed then
>    "  BUILD_INTRUDER(INTRUDER_0) =\n"++
>           "    " ++ intrudername ++ " [| STOP_SET |] STOP\n\n"
>    else
>    "  -- Intruder used for temporal specs\n"++
>    "  BUILD_INTRUDER'(INTRUDER_0,IK) =\n"++
>    "    ("++ intrudername ++ " ||| SAY_KNOWN(IK)) [| STOP_SET |] STOP\n\n"++
>      ifNotFlagString an UnboundedParallel (
>      "  -- Intruder used for all other specs\n"++
>      "  BUILD_INTRUDER(INTRUDER_0) = BUILD_INTRUDER'(INTRUDER_0,IK1)\n\n")
>    )
>    ++"endmodule\n\n"++
>    "-- FDR bug: cannot have a module prefix in a channel type\n"++
>    "Deductions' = INTRUDER_M::COMBINED_DEDUCTIONS\n"++
>    "channel infer : Deductions'\n\n"

======================================================================

>senderReceiverTypes :: Annotated -> Output
>senderReceiverTypes an =
>   "  -- Types of sender and receiver of each message\n\n"++
>   -- The following version is rather naive
>   concat 
>     ["  SenderType (Msg"++n++") = "++ findtype an s ++ "\n" | 
>           (_,n,Agent s,Agent _,_,_,_,_) <- protdesc an] ++
>   "\n" ++
>   concat
>     ["  ReceiverType(Msg"++n++") = "++ findtype an r ++ "\n" | 
>           (_,n,Agent _,Agent r,_,_,_,_) <- protdesc an] ++
>   "\n" 
>   -- The following version is more intelligent, but needs to be extended to 
>   -- deal with messages that have been renamed to their representative member
>   {-
>   concat  
>     ["SenderType ((Msg"++n++", "++snd(showPatMsg s False m)++")) = "++ 
>        senderType an s m ++ "\n" |  
>           (_,n,Agent s,Agent _,m,_) <- protdesc an] ++ 
>   "\n" ++ 
>   concat 
>     ["ReceiverType((Msg"++n++", "++snd(showPatMsg r False m)++")) = "++ 
>        receiverType an r m ++ "\n" |  
>           (_,n,Agent _,Agent r,m,_) <- protdesc an] ++ 
>   -}
