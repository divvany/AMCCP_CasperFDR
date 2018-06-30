Calculate Fact1 and algebraic laws

>module Algebra(makeFactsAndLaws) where

>import Useful
>import Atoms
>import Messages
>import Types
>import Annotated
>import UnboundParallel 

======================================================================

Produce all facts, laws over those facts, and associated variable binding

>makeFactsAndLaws :: Annotated -> ([Msg],[(Msg,Msg)], VarTypeList)
>makeFactsAndLaws an = 
>  let
>   protms = flatten [ m | (_,_,_,_,m,_,_,_) <- protdesc an]
>	-- I need the sequences for unbound parallal attacks
>   -- Also need the sequences for the new channels models
> -- (to enable all deductions from e.g. SentBy)
>       -- FIXME: Needs to be configurable, because it slows 
>       --        down compilation
>   seqms = if hasFlag an UnboundedParallel || not (newchannels an == []) then 
>       [ Sq m | (_,_,_,_,Sq m,_,_,_) <- protdesc an] 
>       else []
>   sentms = if hasFlag an UnboundedParallel then factsFromSentRep an else []
>   secms = [s | Sec _ s _ <- secrets an] ++ 
>               [s | StrongSec _ s _ <- secrets an]
>   (dtim, dtfvts) = makeAllDTMs (dtdefs an)
>   dtms = flatmap snd dtim -- all instances of all datatypes
>   dtAtoms = [v | Atom v <- dtms]
>   allms = remdups (protms++dtms++secms++seqms)
>   allfvts = fvts an++dtfvts
>   eqs' = remdups(equivs an ++ [(cs,m2,m1) | (cs,m1,m2) <- equivs an] ++ builtInLaws)
>   ts = map (allSubsAndEquivs an allfvts dtim dtAtoms eqs' []) allms
>   fact1 = remdups (flatmap (\(s,_,_) -> s) ts ++ sentms)
>   pairs = remdups (flatmap (\(_,_,aps) -> aps) ts)
>   laws = [(m,m') | (m,m') <- pairs, m/=m']
>  in (fact1, laws, allfvts)

Built in algebraic laws

>builtInLaws :: [Equivalence]
>builtInLaws =
>  -- Commutativity of Vernam encryption
>  let vernComm = ([("m1", ""), ("m2", "")], 
>                  Xor (Atom "m1") (Atom "m2"), 
>                  Xor (Atom "m2") (Atom "m1"))
>  -- Associativity of Vernam encryption
>      vernAssoc = ([("m1", ""), ("m2", ""), ("m3", "")], 
>                   Xor (Xor (Atom "m1") (Atom "m2")) (Atom "m3"), 
>                   Xor (Atom "m1") (Xor (Atom "m2") (Atom "m3")))
>  in [vernComm, vernAssoc]

Replace all Sqs by their contents

>flatten :: [Msg] -> [Msg]
>flatten ms = concat [ms' | Sq ms' <- ms] ++ filter notSq ms
>  where notSq (Sq _) = False
>        notSq _ = True

Convert all forward and undec clauses into normal messages.

>convertUndecForwd :: Msg -> Msg
>convertUndecForwd (Undec m v) = convertUndecForwd m
>convertUndecForwd (Forwd v m) = (convertUndecForwd m)
>convertUndecForwd (Atom a) = Atom a
>convertUndecForwd (Encrypt k ms) = Encrypt (convertUndecForwd k) (map convertUndecForwd ms)
>convertUndecForwd (Sq ms) = Sq (map convertUndecForwd ms)
>convertUndecForwd (Xor m1 m2) = Xor (convertUndecForwd m1) (convertUndecForwd m2)
>convertUndecForwd (Apply vn m) = Apply vn (convertUndecForwd m)

========================================================================
Return sets of all instances of datatypes

>type DTInstanceMap = [(TypeName, [Msg])]

A pair (tn,ms) in a DTInstanceMap means that ms is the set of all 
templates for messages in datatye tn.

>makeAllDTMs :: DataTypeDefs -> (DTInstanceMap, VarTypeList)
>makeAllDTMs dtdefs = 
>  let dtis = [(tn, makeDTMs dtdefs (tn,pats,n)) | (tn,pats,n) <- dtdefs]
>      tns = [tn | (tn,_,_) <- dtdefs]++
>            [cons | (_,pats,_) <- dtdefs, (cons,_) <- pats]
>  in renameDTMs tns dtis

Produce set of templates for all instances of datatype definition (dt, pats,
n), with occurences of variables of types other than datatypes represented by
the type name.

>makeDTMs :: DataTypeDefs -> DataTypeDef -> [Msg]
>makeDTMs dtdefs (_, pats, n) =
>  let argset arg = -- list of all instances of arg
>        case [(dt',args',n') | (dt',args',n') <- dtdefs, dt'==arg] of
>          [] -> [Atom arg]
>          [(dt',args',_)] -> makeDTMs dtdefs (dt',args',n-1)
>          _ -> error "argset"
>  in
>  if n==0 then [Atom cons | (cons,[]) <- pats]
>  else [Atom cons | (cons,[]) <- pats]++
>       [Apply cons (if length args'==1 then hd args' else Sq args') |
>          (cons,args) <- pats, args/=[], args' <- cp (map argset args)]

Cartesian product

>cp :: [[a]] -> [[a]]
>cp [] = [[]]
>cp (xs:xss) = let yss = cp xss in [x:ys | x <- xs, ys <- yss]

For each (tn,ms) in dtis, rename each occurence of a typename in ms, other
than those from tns, to a new variable, returning suitable binding.

>renameDTMs :: [TypeName] -> DTInstanceMap -> (DTInstanceMap, VarTypeList)
>renameDTMs tns dtis =
>  let -- do renaming and get binding for each datatype tn
>      tnmvtss = [(tn, map (renameDTM tns) ms) | (tn,ms) <- dtis]
>      -- pick out instances of each datatype tn
>      dtis' = [(tn, map fst mvts) | (tn, mvts) <- tnmvtss]
>      -- pick out and combine bindings
>      dtvts = remdups(concat [vts | (_,mvtss) <- tnmvtss, (_,vts) <- mvtss])
>  in (dtis', dtvts)

Rename each occurence of a typename other than those from tns in m to a new
variable, returning suitable binding

>renameDTM :: [TypeName] -> Msg -> (Msg, VarTypeList)
>renameDTM tns m = 
>  let (m',tc) = renameDTM1 tns [] m 
>  in (m', [(tn++"_"++show i, tn, []) | (tn,n) <- tc, i <- [1..n]])

>type TypeCount = [(TypeName, Int)]

>renameDTM1 :: [TypeName] -> TypeCount -> Msg -> (Msg, TypeCount)
>renameDTM1 tns tc (Atom v) = 
>  if member v tns 
>  then (Atom v, tc)
>  else let (n,tc') = inc tc v in (Atom (v++"_"++show n), tc')
>renameDTM1 tns tc (Sq ms) = 
>  let (ms',tc') = renameDTM1seq tns tc ms in (Sq ms', tc')
>renameDTM1 tns tc (Encrypt k ms) =
>  let (k',tc') = renameDTM1 tns tc k
>      (ms', tc'') = renameDTM1seq tns tc' ms
>  in (Encrypt k' ms', tc'')
>renameDTM1 tns tc (Xor m1 m2) =
>  let (m1',tc') = renameDTM1 tns tc m1
>      (m2',tc'') = renameDTM1 tns tc' m2
>  in (Xor m1' m2', tc'')
>renameDTM1 tns tc (Apply f m) =
>  let (m', tc') = renameDTM1 tns tc m
>  in (Apply f m', tc')


Get number for next occurence of type t, and update tc appropriately

>inc :: TypeCount -> TypeName -> (Int, TypeCount)
>inc tc t = 
>  let matches = filter ((==t) . fst) tc
>      others = filter ((/=t) . fst) tc
>  in case matches of
>       [] -> (1, (t,1):others)
>       [(t,n)] -> (n+1, (t,n+1):others)

Rename sequence of messages

>renameDTM1seq :: [TypeName] -> TypeCount -> [Msg] -> ([Msg], TypeCount)
>renameDTM1seq _ tc [] = ([], tc)
>renameDTM1seq tns tc (m:ms) = 
>  let (m',tc') = renameDTM1 tns tc m
>      (ms', tc'') = renameDTM1seq tns tc' ms
>  in (m':ms', tc'')

=========================================================================

>type MsgPairs = [(Msg, Msg)]

Get submessages of given message, and calculate all pairs formed by applying
equivalences to this message, or to submessages.  Components of result are:
1) all submessages of this message, and all equivalent messages;
2) all pairs derivable immediately from this message;
3) all pairs derivable from this message or from submessages.

>allSubsAndEquivs :: Annotated -> VarTypeList -> DTInstanceMap -> [VarName] -> 
>   [Equivalence] -> [Msg] -> Msg -> ([Msg], MsgPairs, MsgPairs)
>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Atom a) = 
>  let equals = Atom a : equivMsgs an fvts dtAtoms eqs (Atom a)
>      pairs = [(Atom a, m) | m <- equals]
>      atype = findtype an a
>      matches = [ms | (dt,ms) <- dtim, dt==atype]
>  in -- (equals, pairs, pairs)
>  if member a dtAtoms then (equals, pairs, pairs)
>  else
>  case matches of
>    [] -> (equals, pairs, pairs)
>    [ms] -> 
>      let ts = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done) 
>                   (ms\\done)
>          mspairs = flatmap (\(_,ps,_) -> ps) ts
>          msallpairs = flatmap (\(_,_,ap) -> ap) ts
>      in (equals, pairs++mspairs, pairs++msallpairs)
>    _ -> error "allSubsAndEquivs"

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Encrypt k ms) =
>  let -- recursively apply to k and k inverse
>      kinv = inverse2 (fiks an) k
>      (ksubs1, kpairs1, kallpairs1) = 
>        allSubsAndEquivs an fvts dtim dtAtoms eqs done k
>      (ksubs2, _, kallpairs2) = -- ([kinv],[],[])
>        allSubsAndEquivs an fvts dtim dtAtoms eqs done kinv
>      ksubs = remdups(ksubs1++ksubs2)
>      -- kpairs = remdups(kpairs1++kpairs2)
>      kallpairs = remdups(kallpairs1++kallpairs2)
>      -- recursively apply to ms, and unpack
>      ts = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done) ms
>      mssubs = flatmap (\(s,_,_) -> s) ts
>      mspairs = combineSeqPairs (map (\(_,ps,_) -> ps) ts)
>      msallpairs = flatmap (\(_,_,ap) -> ap) ts
>      -- get equivalences, and recursively apply function 
>      equals = remdups (equivMsgs an fvts dtAtoms eqs (Encrypt k ms))
>      done' = remdups (Encrypt k ms:done++ksubs++mssubs)
>      ets = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done') (equals\\done')
>      esubs = flatmap (\(s,_,_) -> s) ets
>      eallpairs = flatmap (\(_,_,ap) -> ap) ets
>      -- build up result
>      subs = remdups (Encrypt k ms : mssubs ++ ksubs ++ 
>                      equals ++ esubs ++ 
>                      [Encrypt k2 ms2 |(_,k2) <- kpairs1, (_,ms2) <- mspairs])
>   -- We convert all undec and forwd nodes into normal nodes before calculating the
>   -- equivalences. This is to stop problems where messages containing garbage
>   -- are equivlaent to a message containing correct decryptions. For an example of
>   -- where this did occur see Tests/Automated/Regressions/DavidWilliams-Algebra-Garbage.spl
>      pairs = 
>        remdups(
>          [(Encrypt k (map convertUndecForwd ms), m') | m' <- equals]++
>          [(Encrypt k1 ms1, Encrypt k2 ms2) | 
>              (k1, k2) <- kpairs1, (ms1, ms2) <- mspairs])
>      allpairs = remdups (pairs ++ kallpairs ++ msallpairs ++ eallpairs 
>                         -- ++
>                         --[(Encrypt k2 ms2, Encrypt k2 ms2) | 
>                         --    (_, k2) <- kpairs1, (_, ms2) <- mspairs]
>                         )
>  in (subs, pairs, allpairs)

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Sq ms) = 
>  let -- recursively apply to ms, and unpack
>      ts = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done) ms 
>      mssubs = flatmap (\(s,_,_) -> s) ts
>      mspairs = combineSeqPairs (map (\(_,ps,_) -> ps) ts) 
>      msallpairs = flatmap (\(_,_,ap) -> ap) ts
>      -- get equivalences, and recursively apply function 
>      equals = equivMsgs an fvts dtAtoms eqs (Sq ms) 
>      done' = remdups (Sq ms:done++mssubs)
>      ets = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done') 
>                (equals\\done')
>      esubs = flatmap (\(s,_,_) -> s) ets
>      eallpairs = flatmap (\(_,_,ap) -> ap) ets
>      -- build up result
>      subs = remdups (Sq ms : mssubs ++ equals ++ esubs ++ 
>                      [Sq ms' | (_,ms') <- mspairs]) 
>      pairs =  
>        remdups(
>          [(Sq ms, m') | m' <- equals]++ 
>          [(Sq ms1, Sq ms2) | (ms1, ms2) <- mspairs])
>      allpairs = remdups (pairs ++ msallpairs ++ eallpairs ++
>                          [(Sq ms', Sq ms') | (_,ms') <- mspairs]) 
>  in (subs, pairs, allpairs) 
>

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Xor m1 m2) = 
>  let -- recursively apply to m1 and m2
>      (subs1, pairs1, allpairs1) = 
>         allSubsAndEquivs an fvts dtim dtAtoms eqs done m1
>      (subs2, pairs2, allpairs2) = 
>         allSubsAndEquivs an fvts dtim dtAtoms eqs done m2
>      -- get equivalences, and recursively apply function 
>      equals = equivMsgs an fvts dtAtoms eqs (Xor m1 m2) 
>      done' = remdups (Xor m1 m2:done++subs1++subs2)
>      ets = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done')
>                (equals\\done')
>      esubs = flatmap (\(s,_,_) -> s) ets
>      eallpairs = flatmap (\(_,_,ap) -> ap) ets
>      -- build up result
>      subs = remdups (Xor m1 m2 : subs1 ++ subs2 ++ equals ++ esubs ++ 
>                      [Xor m1' m2' | (_,m1') <- pairs1, (_,m2') <- pairs2]) 
>      pairs =  
>        remdups(
>          [(Xor m1 m2, m') | m' <- equals]++ 
>          [(Xor m1' m2', Xor m1'' m2'') |
>              (m1', m1'') <- pairs1, (m2', m2'') <- pairs2])
>      allpairs = remdups
>                   (pairs ++ allpairs1 ++ allpairs2 ++ eallpairs ++
>                    [(Xor m1' m2',Xor m1' m2') |
>                        (_,m1') <- pairs1, (_,m2') <- pairs2])
>  in (subs, pairs, allpairs) 

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Undec m v) =
>  let (subs, pairs, allpairs) = 
>        allSubsAndEquivs an fvts dtim dtAtoms eqs done m
>      refpair = (Undec m v, Undec m v)
>  in (subs, refpair : pairs, refpair : allpairs)

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Forwd v m) =
>  let (subs, pairs, allpairs) =
>        allSubsAndEquivs an fvts dtim dtAtoms eqs done m
>      refpair = (Forwd v m, Forwd v m)
>  in (subs, refpair : pairs, refpair : allpairs)

>allSubsAndEquivs an fvts dtim dtAtoms eqs done (Apply f m) =
>  let (msubs, mpairs, mallpairs) = 
>         allSubsAndEquivs an fvts dtim dtAtoms eqs done m
>      -- get equivalences, and recursively apply function 
>      equals = equivMsgs an fvts dtAtoms eqs (Apply f m)
>      done' = remdups (Apply f m:done++msubs)
>      ets = map (allSubsAndEquivs an fvts dtim dtAtoms eqs done') 
>                (equals\\done')
>      esubs = flatmap (\(s,_,_) -> s) ets
>      eallpairs = flatmap (\(_,_,ap) -> ap) ets
>      -- build up result
>      subs = remdups (Apply f m : msubs ++ equals ++ esubs ++
>                      [Apply f m' | (_, m') <- mpairs])
>      pairs = remdups(
>               [(Apply f m, m') | m' <- equals] ++
>               [(Apply f m1, Apply f m2) | (m1,m2) <- mpairs])
>      allpairs = remdups(pairs++mallpairs++eallpairs)
>  in (subs, pairs, allpairs)

Inverse key, as message

>inverse2 :: InverseKeyList -> Msg -> Msg
>inverse2 fiks (Atom k) = Atom (inverse1 fiks k)
>inverse2 fiks (Apply f as) = Apply (inverse1 fiks f) as
>inverse2 fiks (Forwd _ m) = inverse2 fiks m
>inverse2 fiks (Undec m _) = inverse2 fiks m

Combine list of pairs into list of (pairs of lists of messages)

>combineSeqPairs :: [MsgPairs] -> [([Msg], [Msg])]
>combineSeqPairs [] = [([],[])]
>combineSeqPairs (ps:pss) =
>  let ps' = combineSeqPairs pss
>      (m,m') = head ps
>      heads =  map head pss
>      fsts = map fst heads
>      snds = map snd heads
>  in remdups(
>       [(catenate m ms, catenate m' ms') | (ms,ms') <- ps'] ++
>       [(catenate m fsts, catenate m' snds) | (m,m') <- ps])

>catenate (Sq ms) ms' = ms++ms'
>catenate m ms' = m:ms' 

=========================================================================

Messages immediately equivalent to given message under set of equivalences
(with no repetitions).

>equivMsgs an fvts dtAtoms eqs m = 
>  remdups [m' | Just m' <- map (equivMsgs1 an fvts dtAtoms m) eqs, m'/=m]

Try to apply given equivalence to given message to derive new message

>equivMsgs1 :: 
>  Annotated -> VarTypeList -> [VarName] -> Msg -> Equivalence -> Maybe Msg
>equivMsgs1 an fvts dtAtoms m (cs, m1, m2) =
>  case unify fvts (fnts an) dtAtoms [(a,b,[]) | (a,b) <- cs] m m1 of
>    Nothing -> Nothing
>    Just u -> Just (rename u m2)

=========================================================================
Unifying messages from protocol description with messages from equivalences

Type of unifying mappings

>type Unification = [(VarName, Msg)]

Use the convention that phi, etc, are unifying functions, and psi, etc are of
type Maybe Unification

Test whether first message, typed according to fvts, unifies with second
message, typed according to cs, and if so, return unifying function on
variables of second message.

>unify :: 
>  VarTypeList -> FnTypeList -> [VarName] -> VarTypeList -> Msg -> Msg -> 
>         Maybe Unification

>--Datatype constants should only unify with themselves
>unify _ _ dtAtoms _ m (Atom v) | member v dtAtoms = 
>  if m==Atom v then Just [(v, m)] else Nothing

>-- An untyped atom will match anything
>unify _ _ _ cs m (Atom v) | findtype_ cs v=="" = Just [(v, m)]

>unify fvts _ _ cs (Atom a) (Atom v) = 
>  if findtype_ fvts a==findtype_ cs v
>  then Just [(v,Atom a)] 
>  else Nothing

>unify fvts fnts dtAtoms cs (Encrypt k ms) (Encrypt k' ms') =
>  combine (unify fvts fnts dtAtoms cs k k') 
>          (unifySeq fvts fnts dtAtoms cs ms ms')

>unify fvts fnts dtAtoms cs (Sq ms) (Sq ms') = 
>  unifySeq fvts fnts dtAtoms cs ms ms'

>unify fvts fnts dtAtoms cs (Xor m1 m2) (Xor m1' m2') =
>  let psi1 = unify fvts fnts dtAtoms cs m1 m1'
>      psi2 = unify fvts fnts dtAtoms cs m2 m2'
>  in combine psi1 psi2

>-- Two function applications unify iff they're the same functions, and the 
>-- arguments unify
>unify fvts fnts dtAtoms cs (Apply f m) (Apply g m') =  
>  if f==g then unify fvts fnts dtAtoms cs m m' else Nothing

>unify _ fnts _ cs (Apply f m) (Atom v) =
>  if findFnRanType fnts f==findtype_ cs v then Just [(v, Apply f m)] 
>  else Nothing

>unify fvts fnts dtAtoms cs (Undec m _) m' = unify fvts fnts dtAtoms cs m m'  

>unify fvts fnts dtAtoms cs (Forwd _ m) m' = unify fvts fnts dtAtoms cs m m'  

>unify _ _ _ _ _ _ = Nothing

unify sequences of messages

>unifySeq :: 
>  VarTypeList -> FnTypeList -> [VarName] -> VarTypeList -> [Msg] -> [Msg] -> 
>    Maybe Unification
>unifySeq fvts fnts dtAtoms cs ms ms' = 
>  case ms' of
>    [Atom v] | findtype_ cs v=="" -> Just [(v, maybeSq ms)]
>    _ -> if length ms /= length ms' 
>         then Nothing
>         else let us = zipWith (unify fvts fnts dtAtoms cs) ms ms'
>              in foldr1 combine us

>maybeSq [m] = m
>maybeSq ms = Sq ms

combine two unifications, if possible

>combine :: Maybe Unification -> Maybe Unification -> Maybe Unification
>combine Nothing _ = Nothing
>combine _ Nothing = Nothing
>combine (Just phi1) (Just phi2) = combine' phi1 phi2

>combine' phi1 [] = Just phi1
>combine' phi1 ((v,m) : phi2) =
>  let psi' = combine' phi1 phi2
>  in
>  case psi' of 
>    Nothing -> Nothing
>    Just phi' ->
>      case filter ((==v) . fst) phi' of
>        [] -> Just ((v,m) : phi')
>        [(_,m')] -> if m==m' then Just phi' else Nothing

Rename message under unification

>rename :: Unification -> Msg -> Msg
>rename u (Atom v) = 
>  case filter ((==v) . fst) u of
>    [(_,m')] -> m'
>    [] -> Atom v
>    _ -> error ("Casper error 5986 "++show u ++ show v)
>rename u (Sq ms) = Sq (unSeq (map (rename u) ms))
>rename u (Encrypt k ms) = Encrypt (rename u k) (unSeq (map (rename u) ms))
>rename u (Xor m m') = Xor (rename u m) (rename u m')
>rename u (Apply f m) = Apply f (rename u m)

>unSeq [Sq ms] = ms
>unSeq ms = ms



======================= THE END ================================

>{-  "applyRenaming(Sq.ms_) =\n"++
>  "  let S_ = {b_ | (b_,Sq.ms_') <- renaming, ms_==ms_'}\n"++
>  "  within if card(S_)==0 then Sq.<applyRenaming(m_) | m_ <- ms_>\n"++
>  "         else let {b_}=S_ within b_\n"++
>  "applyRenaming(a_) =\n"++
>  "  let S_ = {b_ | (b_,a_') <- renaming, a_'==a_}\n"++
>  "  within if card(S_)==0 then a_ else let {b_}=S_ within b_\n"++ -}

{applyRenaming(a_) | a_ <- X_Some tests

>{-
>testdtms :: [Msg]
>testdtms = 
>  [Atom "Gen",
>   Apply "Exp" (Sq [Atom "Gen",Atom "Num_1"]),
>   Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "Num_1"]),Atom "Num_2"])]

>testdtm = 
>  Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "Num_1"]),Atom "Num_2"])

>testeqs :: [Equivalence]
>testeqs = 
>  [([("x","Num"),("y","Num")],
>    Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "x"]),Atom "y"]),
>    Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "y"]),Atom "x"]))]

>testeqs' =
> [([("x","Num"),("y","Num")],
>   Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "x"]),Atom "y"]),
>   Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "y"]),Atom "x"])),
>  ([("x","Num"),("y","Num")],
>   Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "y"]),Atom "x"]),
>   Apply "Exp" (Sq [Apply "Exp" (Sq [Atom "Gen",Atom "x"]),Atom "y"])),
>  ([("m1",""),("m2","")],
>   Xor (Atom "m1") (Atom "m2"),
>   Xor (Atom "m2") (Atom "m1")),
>  ([("m1",""),("m2",""),("m3","")],
>   Xor (Xor (Atom "m1") (Atom "m2")) (Atom "m3"),
>   Xor (Atom "m1") (Xor (Atom "m2") (Atom "m3")))
> ]

>testfvts = [("Num_1","Num"),("Num_2","Num")]
>testfvts' =
>  [("A","Agent"),("B","Agent"),("x","Num"),("y","Num"),
>   ("expx","Field"),("expy","Field"),("k","Field"),("text","TEXT"),
>   ("Gen","Field"),("Num_1","Num"),("Num_2","Num")]

>testfnts = [("Exp",Symb ["Field","Num"] "Field")]

>test1 = map (allSubsAndEquivs testfvts' testfnts [] testeqs' [])  testdtms
>test2 = 
>  filter (\(m,m') -> m/=m') (remdups (flatmap (\(_,_,aps) -> aps) test1))

>test1' = allSubsAndEquivs testfvts' testfnts [] testeqs' []  testdtm
>test2' = 
>  filter (\(m,m') -> m/=m') (remdups ( (\(_,_,aps) -> aps) test1'))
>-}


