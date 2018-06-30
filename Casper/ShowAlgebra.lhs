Produce definition of Fact_1 and algebraic laws

>module ShowAlgebra(showFacts,showLaws,makeFactsAndLawsExports) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import SecureChannels
>import Types
>import Annotated

>showFacts :: Annotated -> VarTypeList -> [Msg] -> Output
>showFacts an allfvts fact1 = 
>  let fns = remdups [f | Apply f _ <- fact1, not (isHashFunction (fnts an) f)]
>      atomTypes = 
>          remdups (map (\(_,b,_) -> b) allfvts ++ 
>                   [findFnRanType (fnts an) f | f <- fns])
>      nonAtomFacts = filter ((notAtom . fnts) an) fact1
>  in "Fact_1 = " ++ 
>     makeUnion 2
>       ("{Garbage}" : atomTypes ++ 
>        ["{" ++ showMsg_ allfvts (fnts an) (varMsg m) ++ " |\n       " ++ 
>         let vgs = makeVarGens_ allfvts (fnts an) (dtdefs an) (varFields m)
>         in if vgs==[] then "true}" else format 7 ", " vgs ++ "}" |
>                  m <- nonAtomFacts] ++
>        newChannelsFacts an ++
>          (if hasFlag an UnboundedParallel then 
>               ["{ sm_ | (sm_,_) <- INTRUDER_M::All_External_and_Internal_Deductions}"] 
>           else [])) ++ 
>     "\n"

>notAtom :: FnTypeList -> Msg -> Bool
>notAtom _ (Atom _) = False
>notAtom fnts (Apply f _) = isHashFunction fnts f
>notAtom _ _ = True

>newChannelsFacts :: Annotated -> [String]
>newChannelsFacts an = 
>  let
>       Annotated {newchannels = newchans, protdesc = protdes} = an
>  in
>  if newchans == [] then [] 
>  else if sessinfo an == [] then
>    ["{SentTo.(b_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (channelIs ["C","NR-"] (channelSelect n newchans))] ++
>    ["{SentBy.(a_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (channelIs ["NF","NRA-"] (channelSelect n newchans))] ++
>    ["{SentByTo.(a_, b_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", " ++
>    "a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ "), b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (not (
>      channelIs ["C","NR-"] (channelSelect n newchans) ||
>      channelIs ["NF","NRA-"] (channelSelect n newchans) ||
>      channelIs [] (channelSelect n newchans)
>    ))] ++
>    ["{SentByToC.(a_, b_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", " ++
>    "a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ "), b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (not (
>      channelIs ["C","NR-"] (channelSelect n newchans) ||
>      channelIs ["NF","NRA-"] (channelSelect n newchans) ||
>      channelIs [] (channelSelect n newchans)
>    ))]
>  else
>    ["{SentTo.(b_, c_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ "), c_ <- SessionId(Msg" ++ n ++ ")}" |
>    (_,n,Agent a,_,m,_,_,_) <- protdes, (channelIs ["C","NR-"] (channelSelect n newchans))] ++
>    ["{SentBy.(a_, c_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ "), c_ <- SessionId(Msg" ++ n ++ ")}" |
>    (_,n,Agent a,_,m,_,_,_) <- protdes, (channelIs ["NF","NRA-"] (channelSelect n newchans))] ++
>    ["{SentByTo.(a_, b_, c_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", " ++
>    "a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ "), b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ "), c_ <- SessionId(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (not (
>      channelIs ["C","NR-"] (channelSelect n newchans) ||
>      channelIs ["NF","NRA-"] (channelSelect n newchans) ||
>      channelIs [] (channelSelect n newchans)
>    ))] ++
>    ["{SentByToC.(a_, b_, c_, " ++ showMsg an (varMsg m) ++ ") |\n       " ++
>    let vgs = makeVarGens an (varFields m)
>    in if vgs==[] then "true}" else format 7 ", " vgs ++ ", " ++
>    "a_ <- INTRUDER_M::SenderType(Msg" ++ n ++ "), b_ <- INTRUDER_M::ReceiverType(Msg" ++ n ++ "), c_ <- SessionId(Msg" ++ n ++ ")}" |
>    (_,n,_,_,m,_,_,_) <- protdes, (not (
>      channelIs ["C","NR-"] (channelSelect n newchans) ||
>      channelIs ["NF","NRA-"] (channelSelect n newchans) ||
>      channelIs [] (channelSelect n newchans)
>    ))]

======================================================================

Produce definition of algebraic laws

>showLaws :: Annotated -> VarTypeList -> [(Msg,Msg)] -> Output
>showLaws an allfvts laws = 
>  "  -- Algebraic laws, defined as a set of pairs\n\n"++
>  "  laws = "++
>  (if laws==[] then "{(Garbage, Garbage)}\n\n"
>  else makeUnion 4 (map showLaw laws)++"\n") 
>  ++
>  "  -- Calculate transitive closure of algebraic laws, and select\n"++
>  "  -- representative member of each equivalence class\n\n"++
>  "  external mtransclose\n"++
>  "  renaming = mtransclose(laws, Fact_1)\n"++
>  -- Function that takes message and returns relational inverse image
>  "  ren = relational_inverse_image(renaming)\n"
>  ++"\n"++
>  "  -- function that renames non-sequential fact to representative member\n\n"++
>  "  applyRenaming0(a_) =\n"++
>  "    let S_ = ren(a_)\n"++
>  "    within if card(S_)==0 then a_ else elsing(S_)\n"++
>  "\n"++
>  "  elsing({x_}) = x_\n"++
>  "\n"++
>  "  domain = {a_ | (_,a_) <- renaming}\n\n"
>  where 
>   showLaw  (m,m') =
>     "{("++showMsg_ allfvts (fnts an) (varMsg m)++",\n        "++
>     showMsg an (varMsg m')++") |\n          "++
>     format 10 ", " 
>       (makeVarGens_ allfvts (fnts an) (dtdefs an) (remdups (varFields m++varFields m')))++
>     "}"

======================================================================

>makeFactsAndLawsExports :: Annotated -> Output
>makeFactsAndLawsExports an =
>  "  -- function that renames arbitrary fact to representative member\n\n"++
>  "  applyRenaming(Sq.ms_) =\n"++
>  "    if member(Sq.ms_, Fact_1) then applyRenaming0(Sq.ms_) \n"++
>  "    else Sq.<applyRenaming0(m_) | m_ <- ms_>\n"++
>  "  applyRenaming(a_) = applyRenaming0(a_)\n"++
>  "\n"++
>  "  -- function that renames (label, fact, extras) triples\n\n"++
>  "  rmb((l_,m_,extras_)) = \n" ++
>  "    (l_, applyRenaming(m_), applyRenamingToSeq(extras_))\n"++
>  "  rmb4((l_,m_,s_extras_,r_extras_)) = \n" ++
>  "    (l_, applyRenaming(m_), applyRenamingToSeq(s_extras_), \n"++
>  "     applyRenamingToSeq(r_extras_))\n"++
>  "\n"++
>  "  -- lift renaming to sets and to deductions\n\n"++
>  "  applyRenamingToSet(X_) =\n"++
>  "    union({elsing(ren(a_)) | a_ <- inter(X_,domain)},  diff(X_, domain))\n"++
>  "\n"++
>  "  applyRenamingToSeq(X_) = <applyRenaming(e_) | e_ <- X_>\n"++
>  "\n"++
>  "  applyRenamingToDeductions(S_) =\n"++
>  (if hasFlag an GuessablesUsed then
>     "    {(applyRenaming0(f_), l_, applyRenamingToSet(X_)) | (f_,l_,X_) <- S_}"
>   else
>     "    {(applyRenaming0(f_), applyRenamingToSet(X_)) | (f_,X_) <- S_}")
>  ++"\n\n"


