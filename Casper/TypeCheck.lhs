Checking, particularly type checking

>module TypeCheck (typecheck) where

>import List(sort)
>import Prelude

>import Maybe1
>import Useful
>import Pprint
>import Atoms
>import Messages
>import SecureChannels
>import Types
>import TypeCheckUP

>import TypeCheckpd

>infixl 4 `orelse`
>-- type Warning = String

Perform various checks on the input

>typecheck :: Input -> (String, String)
>typecheck (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>           actvts, iks, timestampinfo, inlines, actualAgents, 
>           _, unboundpar, generateSystem, intruderId, intruderInitKnows, intruderProcs,
>	    crackables, deductions, guessables, equivs, channels, newchannels, sessinfo) = 
>  let vts = [(v,t,st) | (v,t,_,st) <- actvts]
>      allTypes = map (\(_,b,_) -> b) fvts ++ [t | (_,Symb _ t) <- fnts]++
>                 [t | (_,Defed _ t) <- fnts]
>      actualAgentAtoms = 
>        [aa | Star aa <- actualAgents] ++ 
>        concat [aas | SeqComp aas <- actualAgents]
>      errors = 
>        typecheckErrors_UP fvts protdesc procs actualAgents actvts unboundpar++
>        --"Check point0\n" ++
>        typecheckpd (fvts, fnts, fiks, dtdefs, procs, protdesc, 
>                     secrets, auths)
>        `orelse`
>        --"Check point1\n" ++
>        checkactualtypeList vts ++
>        checkTypesMatch fvts fnts dtdefs vts ++
>        checkInvKeyList vts iks ++
>        checkTSInfo (any ((== "TimeStamp") . (\ (_,b,_) -> b)) fvts) 
>                    (or [isTimedAuth at | (_,_,at) <- auths])
>                    ([True  | (_,Just _) <- crackables] /= [])
>                    timestampinfo ++
>        --"Check point2\n" ++
>        checkInlines fnts dtdefs vts inlines ++
>	 -- Check the typing of authentication specifications
>       checkAuthSpecType procs auths ++
>	 -- Check the typing of secrecy specifications
>       checkSecrecySpecType procs secrets ++
>       checkTemporalLogicSpecs fvts actvts protdesc temporalSpecs++
>        --"Check point3\n" ++
>        flatmap (flatmap (checktype vts) . snd) actualAgentAtoms ++
>        --"Check point4\n" ++
>        concat 
>          ["Process names in sequential composition not all equal:\n  "++
>           showSeqComp aas++"\n" | 
>             SeqComp aas <- actualAgents, -- pns = map fst aas, 
>             not (allEqual (map fst aas))] ++
>        --"Check point5\n" ++
>        concat 
>          ["Agent identities in sequential composition not all equal:\n  "++
>           showSeqComp aas++"\n" | 
>             SeqComp aas <- actualAgents, -- ids = map (hd.snd) aas, 
>             not (allEqual (map (hd.snd) aas))] ++
>        checktype vts intruderId ++
>        --"Check point6\n" ++
>        flatmap (checkIKDatum vts fnts) intruderInitKnows ++
>        concat ["Unknown type in Crackables: "++t | 
>                  (t,_) <- crackables, t `notElem` allTypes] ++
>        concat ["Unknown type in Guessables: "++t | 
>                  t <- guessables, t `notElem` allTypes] ++
>        flatmap (checkDeduction fvts fnts) deductions ++
>        flatmap (checkEquiv fvts fnts dtdefs) equivs
>        `orelse` 
>        checkActualInverses fvts vts fiks iks 
>        `orelse`
>        fie ++
>        --"Check point7\n" ++
>        if channels /= (Some [], Some [], Some []) && newchannels /= [] then
>        "Cannot mix old and new secure channels\n" else "" ++ checkSessions sessinfo [n | (_,n,Agent a,_,_,_) <- protdesc]
>      warnings = 
>           typecheckWarnings_UP fvts protdesc procs actualAgents actvts unboundpar auths secrets++
>           actualtypeListwarnings vts ++ fiw ++ channelw ++ newchannelw
>      (fie, fiw) = 
>        checkFeatureInteractions (dtdefs/=[]) (deductions/=[]) (guessables/=[]) (equivs/=[]) (temporalSpecs /= [])
>    -- Check the channel lists do not refer to non-existent messages
>      channelw = checkChannels channels [n | (_,n,_,_,_,_) <- protdesc]
>      newchannelw = checkNewChannels newchannels [n | (_,n,_,_,_,_) <- protdesc]
>  in (errors, warnings)

>checkNewChannels cs messages = check ++ collapsed
>  where (ms, _) = unzip cs
>        check = if diffs /= [] then "Warning: the following channels " ++
>                                    "refer to non-existent messages " ++
>                                    commaConcat diffs ++ "\n"
>                               else ""
>        diffs = ms \\ messages
>        (_, collapsed) = collapse cs

>checkChannels (xs, ys, zs) messages = check xs "secret" ++
>                                      check ys "authenticated" ++
>                                      check zs "direct"
>  where
>    check All _ = ""
>    check (Some bs) chantype =
>      if diffs /= [] then "Warning: the following " ++ chantype ++
>                          " channels refer to non-existent messages " ++
>                          commaConcat diffs ++ "\n"
>                     else ""
>      where
>        diffs = bs \\ messages

Check the session info:
* each message should be in exactly one session
* currently: streams not supported
*-- currently: only one type of session supported at once

>checkSessions sessinfo ms = multiplicity
>  where
>    ms' = [n | (_,_,ns) <- sessinfo, n <- ns]
>    ss' = [(s1,s2) | (s1,s2,_) <- sessinfo]
>    missing = ms \\ ms'
>    extra = ms' \\ ms
>    repeats = findRepeats ms'
>    streams = [ns | (2,_,ns) <- sessinfo]
>    multiplicity = (if missing /= [] && sessinfo /= [] then "Error: the following messages do not appear in a session: " ++
>                   commaConcat missing ++ ".\n" else "")++
>                   (if extra /= [] then "Error: some sessions contain non-existent messages (" ++
>                   commaConcat extra ++ ").\n" else "")++
>                   (if repeats /= [] then "Error: the following messages occur in more than one session: " ++
>                   commaConcat repeats ++ ".\n" else "")++
>                   (if streams /= [] then "Error: stream channels are currently unsupported.\n" else "")

                   (if mixed then "Error: currently only one type of channel supported at once.\n" else "")

  where secrets' = [(a, s, findtype_ fvts s, bs) | (a, s, bs) <- secrets]

Should evaluate checkProcessDef only if types all correct 

>showSeqComp aas = 
>  foldr1 foo [pn++"("++commaConcat args++")" | (pn,args) <- aas]
>  where foo xs ys = xs++" ; "++ys

=========================================================================


>-- infixl `orelse`
>orelse :: String -> String -> String
>"" `orelse` st2 = st2
>st1 `orelse` _ = st1

Check function application matches using %-notation (i.e. terms of the form
f(a) % v or v % f(a)) agree on types.

>checkpairtype :: VarTypeList -> (VarName, VarName) -> String
>checkpairtype tl (v,v') = checktype tl v ++ checktype tl v'

=========================================================================
Check actual type list is ok, firstly checks

>checkactualtypeList :: VarTypeList -> String
>checkactualtypeList tl = flatmap checkAllowed (map (\(a,_,_) -> a) tl 
>                           ++ map (\(_,b,_) -> b) tl)

Now warnings

>actualtypeListwarnings :: VarTypeList -> String
>actualtypeListwarnings tl = 
>  maybeString (errors /= [])
>              ("Warning: actual variable(s) "++commaConcat errors++
>               " given multiple types; \n(I'll assume this is deliberate).\n")
> where errors = ctl tl
>       ctl [] = []
>       ctl ((v,_,_):vts)
>         | [v' | (v',_,_) <- vts, v' == v] /= []       = v : ctl vts
>         | otherwise                                 = ctl vts


=========================================================================
Check actual inverse key list


>checkInvKeyList :: VarTypeList -> InverseKeyList -> String
>checkInvKeyList vts iks = flatmap (checkpairtype vts) iks

=========================================================================
For each free variable key in ks, check that each actual value of the same 
type has an inverse declared in iks

1) Check every actual value has at most one inverse; 2) For each free inverse
key pair in fiks, check every actual variable of the same type has a defined
inverse of the same type and symmetricity; 3) For each actual inverse key
pair, check there is a free inverse key pair of the same type.

>checkActualInverses fvts vts fiks iks =
>  checknoreps iks                                        -- (1)
>  `orelse`
>  flatmap (checkfreeinvpair fvts vts iks) fiks           -- (2)
>  ++
>  flatmap (checkactualinvpair fvts vts fiks) iks         -- (3)

Check no actual key has multiply declared inverse

>checknoreps [] = ""
>checknoreps ((k1,k2):iks) = 
>  let ks = map fst iks++map snd iks
>      check k = maybeString (member k ks) 
>                  ("Key "++k++" has multiply declared inverses\n")
>  in check k1 ++ check k2 ++ checknoreps iks

Check every  key of same type as (fk1,fk2) has inverse of correct types and
symmetricity.

>checkfreeinvpair fvts vts iks (fk1,fk2) =
>  let fk1type = findtype_ fvts fk1
>      fk2type = findtype_ fvts fk2
>      fk1typeset = allOfType_ vts fk1type
>      fk2typeset = allOfType_ vts fk2type
>      declaredInvs = map fst iks ++ map snd iks
>      check1 fktypeset = 
>        concat ["Actual key "++k1++" does not have a declared inverse\n" |
>                   k1 <- fktypeset, not (member k1 declaredInvs)]
>  in
>  check1 fk1typeset
>  `orelse`
>  check1 fk2typeset
>  `orelse`
>  concat ["Actual key "++k1++" declared with inverse of wrong type\n" |
>            k1 <- fk1typeset, not ((inverse1 iks k1) `elem` fk2typeset)]
>  `orelse`
>  concat ["Actual key "++k2++" declared with inverse of wrong type\n" |
>            k2 <- fk2typeset, not ((inverse1 iks k2) `elem` fk1typeset)]
>  `orelse`
>  if fk1==fk2 -- symmetric keys
>  then 
>  concat ["Actual key "++k1++
>          " declared as asymmetric when symmetric expected\n" |
>             k1 <- fk1typeset, inverse1 iks k1 /= k1]
>  else 
>  concat ["Actual key "++k1++
>          " declared as symmetric when asymmetric expected\n" |
>             k1 <- fk1typeset, inverse1 iks k1 == k1]

Check fiks contains a free inverse key pair of the same types as (k1,k2)

>checkactualinvpair fvts vts fiks (k1,k2) =
>  let k1types = [t | (v,t,_) <- vts, v == k1]
>      k2types = [t | (v,t,_) <- vts, v == k2]
>      matches = 
>        [(fk1,fk2) | (fk1,fk2) <- fiks, 
>                      let fk1type = findtype_ fvts fk1
>                          fk2type = findtype_ fvts fk2
>                      in fk1type `elem` k1types && fk2type `elem` k2types
>                         || fk1type `elem` k2types && fk1type `elem` k2types]
>  in 
>  maybeString (matches==[]) 
>     ("Inverse key pair ("++k1++", "++k2++
>      ") not matched by free inverse key pair\n")

=========================================================================
Check types of free variables agree with types of actual variables

>checkTypesMatch :: VarTypeList -> FnTypeList -> DataTypeDefs ->VarTypeList -> String
>checkTypesMatch fvts  fnts dtdefs vts =
>  concat
>   (["Type "++ft++" of free variables not matched by any actual values\n" | 
>        ft <- fTypes, not (member ft (aTypes++casperTypes++sTypes++dTypes))] ++ 
>    -- this should deal with inline functions
>    ["Type "++t++" of actual values not matched by any free variables\n" | 
>        t <- aTypes, not (member t fTypes)] ++
>    ["Variable "++v++" appears as both free variable and actual value\n" |
>        v <- map (\(a, _, _) -> a) fvts, member v (map (\(a,_,_) -> a) vts)])
>  where fTypes = -- types of free variables and ranges of non-symbolic fns
>          remdups (map (\(_,b,_) -> b) fvts ++ [rt | (_, Defed _ rt) <- fnts])
>        aTypes = remdups (map (\(_,b,_) -> b) vts)  -- types of actual variables
>        sTypes = [rt | (_, Symb _ rt) <- fnts]
>        casperTypes = ["Bool", "TimeStamp", "HashFunction"]
>        dTypes = [t | (t,_,_) <- dtdefs]

=========================================================================

Check timestamp info.  First argument represents whether timestamps are used
in messages.  Second argument represents whether time is used in any
authentication.  Third argument represents whether time is used in key
compromise.

>checkTSInfo :: Bool -> Bool -> Bool -> TimeStampInfo -> String
>checkTSInfo True  _   _ NotUsed         = "No definition for TimeStamp\n"
>checkTSInfo False ta tc NotUsed         = 
>  if ta || tc then "No definition for MaxRunTime" else ""
>
>checkTSInfo True  _  _  (MRTUsed _) = "No definition for TimeStamp\n"
>checkTSInfo False ta tc (MRTUsed _) = 
>    if ta || tc then "" else "Unnecessary definition of MaxRunTime\n"
>
>checkTSInfo False _  _   (TimeStampsUsed _ _ _) = 
>    "Unnecessary definition of TimeStamp\n"
>checkTSInfo True  _  _   (TimeStampsUsed t0 t1 _) 
>  | t0 > t1      = "Bad definition for TimeStamp\n"
>  | otherwise    = ""

======================================================================
Check the typing of authentication specifications

Condition: For all (A, B, authtype) in auths,
		A, B must be a member of [id | (id,_,_,_,_) <- procs]

>checkAuthSpecType procs auths =
>  let	procsId = [id | (id,_,_,_,_) <- procs]
>	authAgents = concat[[r,c] | (r,c,_) <- auths]
>	badTypes = authAgents \\ procsId
>  in
>	concat
>	 ["Error: The following variable(s) (in the authentication " ++
>	  "specifications):\n" ++
>	  commaConcat badTypes ++ ", must each match\n" ++
>	  "a process identity declared in #Processes.\n\n" |
>		badTypes /=[]]


======================================================================
Check the typing of secrecy specifications

Condition: For all Sec A X LS and StrongSec B Y MS in secrets,
		For all i:(A:B:(LS++MS)),
			member i [id | (id,_,_,_,_) <- procs]

>checkSecrecySpecType procs secrets =
>  let	procsId = [id | (id,_,_,_,_) <- procs]
>	secAgents = concat([(a:ls) | Sec a _ ls <- secrets] ++
>		           [(a:ls) | StrongSec a _ ls <- secrets])
>	badTypes = secAgents \\ procsId
>  in
>	concat
>	 ["Error: The following variable(s) (in the secrecy " ++
>	  "specifications):\n" ++
>	  commaConcat badTypes ++ " must each match\n" ++
>	  "a process identity declared in #Processes.\n\n" |
>		badTypes /=[]]



======================================================================
Check inline functions

>checkInlines fnts dtdefs vts inlines =
>  let	alldecfns = [f | (f,t) <- fnts, t /= HashFunction] -- map fst fnts
>	allexpfns = [f | Defined (f,_,_) <- inlines]
>	allsymfns = [f | Symbolic f <- inlines] 
>	allinlinefns = [f | Inline (f,_,_) <- inlines]
>	alldtconss = [cons | (_,pats,_) <- dtdefs, (cons, _:_) <- pats]
>	alldeffns = allexpfns++allsymfns++allinlinefns++alldtconss
>       pairs = [("hash", [f | (f,HashFunction) <- fnts]),
>                ("symbolic", allsymfns), ("explicit", allexpfns), 
>                ("inline", allinlinefns)] 
>  in
>  flatmap (checkInline fnts vts) inlines ++
>  concat ["Declared function "++f++" not matched by any definition\n" | 
>            f <- alldecfns, not (member f alldeffns)] ++
>  concat ["Function "++f++" declared both as "++fst(pairs!!i)++
>          " function and "++fst(pairs!!j)++" function\n" |
>            i <- [0..3], j <- [i+1..3], f <- snd(pairs!!i), 
>            member f (snd(pairs!!j))]

concat ["Function "++f++" declared both explicitly and symbolically\n" |
            f <- allexpfns, member f allsymfns]

>checkInline fnts vts (Defined (f, as, rhs)) =
>  let errs1 = checkfntype fnts f ++ 
>              flatmap (checktype (vts ++ [("_","_dummy_", [])])) as
>  in 
>  if errs1 /= "" then errs1 
>  else 
>  let ats = findFnDomType fnts f 
>  in
>  if length as /= length ats  
>  then "Function "++f++" defined with wrong arity (expected "++
>        show (length ats)++" found "++show (length as)++")\n"++show ats++"\n"
>  else 
>  let errs2 = 
>        concat ["Argument "++a++" of function "++f++" of wrong type\n" | 
>                      (a,at) <- zip as ats, a /= "_", findtype_ vts a /= at]
>        ++ checktype vts rhs
>  in 
>  if errs2 /= "" then errs2
>  else 
>    let rantype = findFnRanType fnts f  
>        vts' = vts++[("true", "Bool", []), ("false", "Bool", [])]  
>    in maybeString (findtype_ vts' rhs /= rantype)
>             ("Function "++f++" returns result "++rhs++
>              " of unexpected type: expected "++rantype++"\n")
>checkInline fnts _ (Symbolic f) = checkfntype fnts f
>checkInline _ _ (Inline _) = ""

=============================================================================
Check intruder's knowledge

>checkIKDatum vts fnts (Atom a) = 
>  checktype1 vts fnts a ++
>  maybeString (isFn fnts a && isHashFunction fnts a)
>              "Hash functions not allowed in IntruderKnowledge\n"
>checkIKDatum vts fnts (Apply f m) = 
>  case findFnType fnts f of
>    Error e -> e
>    Yes HashFunction -> ""
>    Yes _ -> checkFnApp2 vts fnts {- dtds -} (f,m)
>checkIKDatum vts fnts (Encrypt k ms) = 
>  checkIKDatum vts fnts k ++ flatmap (checkIKDatum vts fnts) ms

=============================================================================
Check deductions; check that
(1) all types in cs are proper types;
(2) no percents in messages;
(3) all free variables "typed" in cs;
(4) all free variables are allowed (not reserved words)

>checkDeduction :: VarTypeList -> FnTypeList -> Deduction -> String
>checkDeduction fvts fnts (cs, ms, m) = 
>  let decvars = map fst cs
>      msgVars = remdupsmerge (atoms m) (sortremdupsconcat (map atoms ms))
>  in
>  concat
>    ["Unrecognized type in deduction: "++t++"\n" |
>       (_,t) <- cs, not (isAType fvts fnts t)]
>  --                                                               (1)
>  ++
>  maybeString (not (noPerCents m && all noPerCents ms))
>              "% used in deduction\n"
>  --                                                               (2)
>  ++
>  concat
>    ["Untyped variable in deduction: "++a++"\n" |
>        a <- msgVars, not (member a decvars)]
>  --                                                               (3)
>  ++
>  flatmap checkAllowed decvars 
>  --                                                               (4)


======================================================================
Check algebraic equivalence; check that
(1) all types in cs are proper types;
(2) no percents in messages;
(3) all free variables "typed" in cs;
(4) all free variables are allowed (not reserved words)
(5) Free variables of both sides are the same
(6) All functions are declared
(7) No explicitly defined functions

>checkEquiv :: 
>  VarTypeList -> FnTypeList -> DataTypeDefs -> Equivalence -> String
>checkEquiv fvts fnts dtdefs (cs, m1, m2) =
>  let decvars = map fst cs++flatmap dtAtoms dtdefs
>      --ats1 = atoms m1
>      --ats2 = atoms m2
>      fns = remdupsmerge (map fst (fnApps m1)) (map fst (fnApps m2))
>      isDefed (Error _) = False
>      isDefed (Yes (Defed _ _)) = True
>      isDefed _ = False
>  in
>  concat
>    ["Unrecognized type in equivalence: "++t++"\n" |
>       (_,t) <- cs, not (isAType fvts fnts t), 
>       t/="Message", t/=""]  -- t/="Message*", 
>  --                                                               (1)
>  ++
>  maybeString (not (noPerCents m1 && noPerCents m2))
>              "% used in equivalence\n"
>  --                                                               (2)
>  ++
>  concat
>    ["Untyped variable in equivalence: "++a++"\n" |
>        a <- remdupsmerge (atoms m1) (atoms m2), not (member a decvars)]
>  --                                                               (3)
>  ++
>  flatmap checkAllowed decvars 
>  --                                                               (4)
>  -- ++
>  -- concat
>  --   ["Free variable "++a++" appears in only one side of an equivalence\n" |
>  --       a <- (ats1 \\ ats2) ++ (ats2 \\ ats1)]
>  --                                                               (5)
>  ++
>  concat
>    ["Undeclared function in equivalence: "++f++"\n" | 
>        f <- fns, isError (findFnType fnts f)] 
>  --                                                               (6)
>  ++
>  concat 
>    ["Explicitly defined function "++f++" used in equivalence\n" | 
>       f <- fns,
>       isDefed (findFnType fnts f)]
>  --                                                               (7)

===================================================================

Check for interaction of features

>checkFeatureInteractions dtUsed deductionsUsed guessablesUsed equivsUsed temporalSpecsUsed =
>  let untestedWarning f1 f2 = 
>        "You are trying to use together two features, "++f1++" and\n"++f2++
>        ", that have not been tested together.  Good luck.\n"
>      errs = 
>        (maybeString (deductionsUsed && guessablesUsed)
>          "Deductions may not be used with guessable values")++
>        (maybeString (guessablesUsed && temporalSpecsUsed)
>           "Temporal specs may not be used with guessable values.")       
>      warnings = 
>        maybeString (guessablesUsed && equivsUsed) 
>          (untestedWarning "guessable values" "algebraic equivalences")
>        ++
>        maybeString (guessablesUsed && dtUsed) 
>          (untestedWarning "guessable values" "data types")
>  in (errs, warnings)

===================================================================

>checkTemporalLogicSpecs :: VarTypeList -> ActVarTypeList -> ProtDesc ->
>   [TemporalLogicSpec] -> String
>checkTemporalLogicSpecs fvts actvts protdesc temporalSpecs = 
>   flatmap checkSpec (zip temporalSpecs [1..])
>   where
>       checkSpec (f,n) = 
>           if res /= "" then "Errors in temporal spec "++show n++":\n"++res else ""
>           where res = checkSpec' (f,n)
>       checkSpec' (f,n)= 
>           (maybeString (concurrentDoeses f > 1)  
>               ("Formula not satisfiable because more than two events "++
>               "are required to occur simultaneously."))
>           ++
>           checkEvents f++
>           (maybeString (not (checkFormula f) )
>               ("Formula is invalid as the left hand side of an implication must be "++
>                "equivlent to a conjunction containing one atomic event that is not "++
>                "inside a previously clause.\n")
>           )
>       checkEvents (Does (agentId,otherAgentId,parity,msgNo,varsToBind)) =
>               if messageIsUnknown then
>                   "  Message "++msgNo++" does not exist.\n"
>               else if unknownFreeVars /= [] then
>                   "  Variables "++commaConcat unknownActualVars++" are unknown free variables.\n"
>               else if unknownActualVars /= [] then
>                   "  Variables "++commaConcat unknownActualVars++" are unknown actual variables.\n"
>               else if remdups freeVarsToBind /= freeVarsToBind then
>                   "  Variables "++commaConcat (listMultiples freeVarsToBind)++
>                   " are bound multiple times within message "++msgNo++".\n"
>               else if not (subset freeVarsToBind msgAtoms) then
>                   "  Variables "++commaConcat (freeVarsToBind \\ msgAtoms)++
>                   " are bound but are not contained within message "++msgNo++".\n"
>               else if incorrectSubs /= [] then
>                   "  Substitutions "++commaConcat formattedSubs++" are not type correct.\n"
>               else ""
>           where
>               freeVars = [fv | (fv,_,_) <- fvts]
>               actVars = [av | (av,_,_,_) <- actvts]
>               unknownFreeVars = 
>                   (remdups ([fv | FreeVar fv <- varsToBind]++[fv | Substitution fv _ <- varsToBind])) \\ freeVars
>               unknownActualVars = 
>                   (remdups [actVar | Substitution _ actVar <- varsToBind]) \\ actVars
>               incorrectSubs = 
>                   [(fv,actVar) | Substitution fv actVar <- varsToBind, 
>                                   findtype_ fvts fv /= hd [t | (av,t,_,_) <- actvts, av == actVar]]
>               formattedSubs = map (\(fv,actvar) -> actvar++" for "++fv) incorrectSubs
>               freeVarsToBind = 
>                   sort ([v | FreeVar v <- varsToBind]++
>                                [v | Substitution v _ <- varsToBind])
>               -- Message from the protocol description
>               messageIsUnknown = length (filter (\(_,n,_,_,_,_) -> n == msgNo) protdesc) == 0
>               (_, _, _, _, m, _) =
>                   head (filter (\(_,n,_,_,_,_) -> n == msgNo) protdesc)
>               msgAtoms = if parity == Send then atomsSend m else atomsRec m
>       checkEvents (Previously f) = checkEvents f
>       checkEvents (And f1 f2) = checkEvents f1++checkEvents f2
>       checkEvents (Or f1 f2) = checkEvents f1++checkEvents f2
>       checkEvents (AlwaysIf f1 f2) = checkEvents f1 ++ checkEvents f2
>       -- Returns the number of Does e events that are required to occur 
>       -- simultainiously
>       concurrentDoeses (Does e) = 1
>       concurrentDoeses (Previously f1) =
>           if concurrentDoeses f1 > 1 then concurrentDoeses f1 else 0
>       concurrentDoeses (And f1 f2) = 
>           concurrentDoeses f1 + concurrentDoeses f2
>       concurrentDoeses (Or f1 f2) = 
>           concurrentDoeses f1 `max` concurrentDoeses f2
>       concurrentDoeses (AlwaysIf f1 f2) = 
>           -- We require a previous to be at the top of the RHS (or and prev || prev...)
>           if concurrentDoeses f2 == 0 then concurrentDoeses f1
>           else concurrentDoeses f2

>       -- Check that the top level of the LHS of an implication there is a does
>       -- event surrounded only be conjunctions (we disallow disjunctions at
>       -- the top level).
>       checkFormula (AlwaysIf f1 f2) = checkFormula' f1
>       checkFormula' (Does e) = True
>       checkFormula' (And f1 f2) = checkFormula' f1 || checkFormula' f2
>       checkFormula' _ = False
