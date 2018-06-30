Typechecking, etc of protocol definition

>module TypeCheckpd 
>  (typecheckpd,
>   maybeString, checkAllowed, 
>   checktype, checktype1, checkfntype,
>   checkFnApp2
>  )
>where

>import Maybe1
>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types

>infixl 4 `orelse`
>orelse :: String -> String -> String
>"" `orelse` st2 = st2
>st1 `orelse` _ = st1

>typecheckpd :: Inputpd -> String
>typecheckpd (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths) =
>  let freeAgents = [id | (id,_,_,_,_) <- procs]
>  in    checkfreetypeList fvts ++
>        checkFnList fvts fnts ++ 
>        checkFreeInvKeyList fvts fnts fiks ++ 
>        checkDTDefs fvts dtdefs ++
>        flatmap (checkProcess fvts fnts) procs  ++ 
>        concat [checktype fvts v | 
>                   (_,_,_,_,m,_) <- protdesc, v <- atoms m] ++ 
>        concat [checkFnApp fvts fnts (f,m') |  
>                   (_,_,_,_,m,_) <- protdesc, (f,m') <- fnApps m]
>        `orelse`
>        --"TypeCheckpd Check point1\n" ++ 
>        concat [let err1 = checktype fvts v  
>                in if err1/="" then err1 else checkPerCent fvts fnts (f,v) | 
>                   (_,_,_,_,m,_) <- protdesc, (f,v) <- fnPerCents m,  
>                   not (isHashFunction fnts f)] ++ 
>        --"TypeCheckpd Check point2\n" ++ 
>        concat [checkInverseKeys fvts fnts fiks m | (_,_,_,_,m,_) <- protdesc] ++ 
>        checkDistinctMsgNos [n | (_,n,_,_,_,_) <- protdesc] ++ 
>        flatmap (checkSecret fvts fnts) secrets ++ 
>        flatmap (checkAuth fvts freeAgents) auths ++ 
>        concat ["Agent "++a++" not represented by a process\n" |  
>                   (_,_,Agent a,_,_,_) <- protdesc,  
>                   not (member a freeAgents)] ++ 
>        concat ["Agent "++a++" not represented by a process\n" |
>                   (_,_,_,Agent a,_,_) <- protdesc,
>                   not (member a freeAgents)] 

Check all keys have declared inverse

>checkInverseKeys fvts fnts fiks m = 
>  concat ["Inverse not declared for key "++k++"\n" | 
>            Atom k <- keys m, not (member k decKeys)]
>  ++
>  concat ["Inverse not declared for key function application "++
>          f++"("++showFn fnts (showMsg_ fvts fnts) m ++")\n" |
>            Apply f _ <- keys m, not (member f decKeys)]
>  where decKeys = map fst fiks ++ map snd fiks

=========================================================================

--  >maybeString :: Bool -> String -> String
--  >maybeString True st = st
--  >maybeString False _ = ""

>checktype :: VarTypeList -> VarName -> String
>checktype tl v =
>  let tl' = tl++[("true", "Bool", []), ("false", "Bool", [])]
>      matches = [t | (v',t,_) <- tl', v==v']
>  in 
>  maybeString (matches == []) ("Undeclared variable: " ++ v ++ "\n")

>checktype1 :: VarTypeList -> FnTypeList -> VarName -> String
>checktype1 tl fnts v = 
>  maybeString 
>    (all (\ (v', _, _) -> v/=v') tl && all (\ (f, _) -> v/=f) fnts)
>    ("Undeclared variable: " ++ v ++ "\n")

>checkfntype :: FnTypeList -> VarName -> String
>checkfntype fnts v = 
>  maybeString (all (\ (f, _) -> v/=f) fnts)
>              ("Undeclared function: " ++ v ++ "\n")

Check function application is of right type (i.e. all arguments are of
expected types).

>checkFnApp :: 
>  VarTypeList -> FnTypeList -> {- DataTypeDefs -> -} (VarName, Msg) -> String
>checkFnApp fvts fnts {- dtds -} (f,m) =
>  case findFnType fnts f of
>    Error e -> e
>    Yes HashFunction -> ""
>    Yes _ -> checkFnApp1 fvts fnts {- dtds -} (f,m)

>checkFnApp1 :: VarTypeList -> FnTypeList -> {- DataTypeDefs -> -} (VarName, Msg) -> String
>checkFnApp1 fvts fnts {- dtds -} (f,m) =
>  let args = (case m of Sq as -> as; a -> [a])
>  in
>  let errs1 = checkfntype fnts f ++ flatmap (checkAtomField fvts fnts) args
>  in 
>  if errs1 /= "" then errs1 
>  else 
>  let ats =  findFnDomType fnts f 
>  in
>  if length args /= length ats  
>  then "Function "++f++" applied to argument of wrong arity\n"
>  else concat ["Argument "++show a++" of function "++f++" of wrong type\n" | 
>                  (a,at) <- zip args ats, fnOrAtomType fvts fnts a /= at]

>fnOrAtomType fvts _ (Atom a) = findtype_ fvts a
>fnOrAtomType _ fnts (Apply f _) = findFnRanType fnts f
>fnOrAtomType fvts fnts (Forwd _ m) = fnOrAtomType fvts fnts m
>fnOrAtomType fvts fnts (Undec m _) = fnOrAtomType fvts fnts m



Similar function, but for actual values, where a value may have multiple types

>checkFnApp2 :: VarTypeList -> FnTypeList -> (VarName, Msg) -> String
>checkFnApp2 vts fnts  (f,m) =
>  let args = (case m of Sq as -> as; a -> [a])
>  in
>  let errs1 = checkfntype fnts f ++ flatmap (checkAtomField vts fnts) args
>  in 
>  if errs1 /= "" then errs1 
>  else 
>  let ats =  findFnDomType fnts f 
>  in
>  if length args /= length ats  
>  then "Function "++f++" applied to argument of wrong arity\n"
>  else concat ["Argument "++show a++" of function "++f++" of wrong type\n" | 
>                  (a,at) <- zip args ats, 
>                  not (member at (fnOrAtomType1 vts fnts a))]

>fnOrAtomType1 vts _ (Atom a) = allTypes_ vts a
>fnOrAtomType1 _ fnts (Apply f _) = [findFnRanType fnts f]
>fnOrAtomType1 vts fnts (Forwd _ m) = fnOrAtomType1 vts fnts m
>fnOrAtomType1 vts fnts (Undec m _) = fnOrAtomType1 vts fnts m


>checkPerCent fvts fnts (f,v) = 
>  maybeString (findFnRanType fnts f /= findtype_ fvts v) 
>    ("Type of "++v++" does not agree with type returned by "++f++
>     " in %-construct\n")

Check atomic field, which should be either variable or function application

>checkAtomField :: VarTypeList -> FnTypeList -> Msg -> String
>checkAtomField fvts _ (Atom v) = checktype fvts v
>checkAtomField fvts fnts (Apply f m) = checkFnApp fvts fnts (f,m)
>checkAtomField fvts fnts (Forwd _ m) = checkAtomField fvts fnts m
>checkAtomField fvts fnts (Undec m _) = checkAtomField fvts fnts m
>checkAtomField _ _ _ = "Variable or function application expected\n"


===========================================================================
Check whether word is allowed

>checkAllowed w
>  | member w reservedWords  = "Illegal use of reserved word: "++w++"\n"
>  | last w == '_'           = "Illegal trailing underscore in word: "++w++"\n"
>  | otherwise 
>      = concat
>        ["Illegal prefix "++w'++" of identifier "++w++"\n" | 
>           w' <- reservedPrefixes, prefix w' w]

>prefix w w' = take (length w) w' == w

>reservedWords = 
>  -- elements of datatypes
>  ["Sq", "Encrypt", "Garbage", "Claim_Secret", "Timestamp", "Hash",
>  -- names of datatypes
>  "Encryption", "Labels", "ROLE", "Signal", "Hash",
>  -- sets
>  "ALL_KEYS", "ALL_PRINCIPALS", "ALL_SECRETS", 
>  "Fact_0", "Deductions_0", "EncryptionDeductions", "DecryptionDeductions",
>  "Deductions", "Fact", "IK0", "IK1", "Sigma", "TS", "TIMEDMSGS",
>  -- functions
>  "inverse", "SenderType", "ReceiverType", "encrypt", "decrypt", -- "subset", 
>  "decryptable", "nth", "max", "min", "TimedMsgs",
>  -- channels
>  "receive", "send", "env", "signal", "leak", "input", "output", 
>  "hear", "say", "infer", "tock", "time",
>  -- processes
>  "KNOWS", "IGNORANT", "SAY_KNOWN", "INTRUDER_0", "BUILD_INTRUDER", "INTRUDER",
>  "SYSTEM", "SYSTEM_0", "TOCKS", "TSKIP", "allowInitTocks", "addTime",
>  "maxDelay", "CLOCK",
>  -- misc
>  "now",
>  -- CSP reserved words
>  "and", "or", "not", "if", "then", "else", "let", "within", "lambda",
>  "ldot", "STOP", "SKIP", "true", "false", "channel", "datatype", 
>  "transparent", "CHAOS", "card", "Inter", "Union", "diff", "union", "head",
>  "inter", "member", "elem", "print", "Set", "Seq", "chase", "assert"]

>reservedPrefixes = 
>  ["Msg", "Env", "Running",  "Commit",  "Alpha", "MSG", "ENV", 
>  "AGENT", "SECRET_SPEC", "AUTH_SPEC", "TIMED_"]


=========================================================================
Check free type list is ok

>checkfreetypeList :: VarTypeList -> String
>checkfreetypeList tl = 
>  maybeString (errors /= [])
>              ("Multiply declared variable(s): "++commaConcat errors++"\n") ++
>  flatmap checkAllowed (map (\(a,_,_) -> a) tl ++ map (\(_,b,_) -> b) tl)
> where errors = ctl tl
>       ctl [] = []
>       ctl ((v,_,_):vts) 
>         | [v' | (v',_,_) <- vts, v' == v] /= []   = v : ctl vts
>         | otherwise                               = ctl vts

=========================================================================
Check all declared functions have domain types that are declared

>{-
>checkFnList fvts fnts = 
>  let allDeclaredTypes = map (\(_,b,_) -> b) fvts
>      foo (f, dts) = 
>         flatmap 
>           (\ dt -> maybeString (not (member dt allDeclaredTypes)) 
>                  ("Domain type "++dt++" of function "++f++" not declared\n"))
>           dts
>      checkFn (f, Symb dts at) = foo (f, dts)
>      checkFn (f, Defed dts at) = foo (f, dts)
>      checkFn (f, HashFunction) = ""
>  in flatmap checkFn fnts
>-}

Iterate, at each stage removing from function type list those functions all of
whose domain types are declared

>checkFnList fvts fnts =
>  let iter allTypes fnts' =
>        let good = all (\ dt -> member dt allTypes) . argsOf
>            fnts'' = filter (not . good) fnts'
>            ok = filter good fnts'
>            newTypes = [at | (_,Symb _ at) <- ok]++[at | (_,Defed _ at) <- ok]
>        in if fnts''==[] then "" -- all types ok
>           else if ok==[] then -- some types not ok
>             concat
>               ["Domain type "++dt++" of function "++f++" not declared\n" |
>                  (f,z) <- fnts', dt <- argsOf(f,z), not(member dt allTypes)]
>           else iter (remdups (allTypes++newTypes)) fnts''
>  in iter (map (\(_,b,_) -> b) fvts) fnts

>argsOf(_,Symb dts _) = dts
>argsOf(_,Defed dts _) = dts
>argsOf(_,HashFunction) = []

=========================================================================

For every pair in the free inverse key list, check each is a declared
variable, or each is a declared function.

>checkFreeInvKeyList :: VarTypeList -> FnTypeList -> InverseKeyList -> String
>checkFreeInvKeyList vts fnts iks = flatmap checkFreeInvKeyPair iks
>  where checkFreeInvKeyPair (v, v') 
>          | member v allvars && member v' allvars || 
>             member v allfns && member v' allfns       
>                      = ""
>          | otherwise = "Error in inverse pair: " ++ v ++ ", " ++ v' ++ "\n"
>        allvars = map (\(a,_,_) -> a) vts
>        allfns = map fst fnts

=========================================================================

Check all detatype definitions:
(1) Different datatypes should have distinct names;
(2) Constructors should have distinct names from types;
(3) Unwinding factors should be consistent: if a datatype with unwinding 
factor n refers to a datatype with unwinding factor n' then we should have
n <= n'+1.

>checkDTDefs :: VarTypeList -> DataTypeDefs -> String
>checkDTDefs fvts dtdefs = 
>  let dtnames = [tn | (tn,_,_) <- dtdefs]
>  in 
>  checkDistinctNames dtnames                                    -- (1)
>  `orelse`
>  flatmap (checkDTDef fvts dtdefs) dtdefs

Check datatype names are distinct

>checkDistinctNames [] = ""
>checkDistinctNames (n:ns) =
>  if member n ns  
>  then "Repeated datatype name: "++n++"\n" ++ checkDistinctNames ns
>  else checkDistinctNames ns

Check single detatype definition

>checkDTDef:: 
>  VarTypeList -> DataTypeDefs -> DataTypeDef -> String
>checkDTDef fvts dtdefs (_, pats, n) = 
>  let allDeclaredTypes = map (\(_,b,_) -> b) fvts
>      conss = [cons | (cons,_) <- pats]
>      deptypes = -- types used in pats
>        concat [ts  | (_, ts) <- pats]
>  in concat 
>       ["Attempt to redefine identifier "++cons++"\n" | 
>           cons <- conss, member cons allDeclaredTypes] ++        -- (2)
>     concat [checkUnwinding dtdefs n t | t <- deptypes]

Check that if t is a datatype then it has unwinding factor at least n-1

>checkUnwinding :: DataTypeDefs -> Int -> TypeName -> String
>checkUnwinding dtdefs n t =
>  let matches = [n' | (t',_,n') <- dtdefs, t==t']
>  in case matches of
>       [] -> ""
>       [n'] -> 
>         if n' < n-1 
>         then "Insufficient unwinding factor "++show n'++" for "++t++
>              " (should be at least "++show (n-1)++")\n"
>         else ""
>       _ -> error "checkUnwinding"

  let subtypes = -- types used in pats
        concat [ts  | (cons, ts) <- pats]
      allDeclaredTypes = map snd fvts
  in concat ["Type "++t++" not declared\n" | t <- subtypes, not (member t allDeclaredTypes)]

=========================================================================
Type check process definition

>checkProcess :: VarTypeList -> FnTypeList -> ProcessInfo -> String
>checkProcess fvts fnts (id, procname, args, knows, generates) =
>  flatmap (checktype fvts) args ++ 
>  flatmap (checktype fvts) generates ++
>  flatmap (checkKnows fvts fnts) knows ++
>  checktype fvts id ++ 
>  maybeString (args == [] || id /= hd args) 
>              ("In process " ++ procname ++ 
>               ", first argument does not match agent's identity\n")

>checkKnows _ fnts (Atom a) = checkfntype fnts a
>checkKnows fvts fnts (Apply f (Sq as)) = 
>  let argerrs = flatmap (\ (Atom a) -> checktype fvts a) as
>  in if argerrs /= "" then argerrs else checkFnApp fvts fnts (f,Sq as)
>checkKnows fvts fnts (Apply f (Atom a)) = 
>  let argerrs = checktype fvts a
>  in if argerrs /= "" then argerrs else checkFnApp fvts fnts (f,Atom a)

=========================================================================
Check message numbers are distinct

>checkDistinctMsgNos [] = ""
>checkDistinctMsgNos (n:ns)          
>  | member n ns  
>           = "Repeated message number: "++n++"\n" ++ checkDistinctMsgNos ns
>  | otherwise   
>           = checkDistinctMsgNos ns

=========================================================================

>checkSecret :: VarTypeList -> FnTypeList -> Secret -> String
>checkSecret fvts fnts (Sec a s bs) =
>  checktype fvts a ++ checkSecMsg fvts fnts s ++ 
>  flatmap (checktype fvts) bs
>checkSecret fvts fnts (StrongSec a s bs) =
>  checktype fvts a ++ checkSecMsg fvts fnts s ++ 
>  flatmap (checktype fvts) bs

>checkSecMsg fvts fnts s = 
>  concat [checktype fvts v | v <- atoms s] ++
>  concat [checkFnApp fvts fnts (f,m) | (f,m) <- fnApps s]

=========================================================================

>checkAuth :: VarTypeList -> [AgentId] -> Auth -> String
>checkAuth fvts agents (a,b,at) =
>  checktype fvts a ++ checktype fvts b ++ 
>  flatmap (checktype fvts) (authArgs at) ++
>  maybeString (not (member a agents)) 
>              ("In authentication specification, agent "++a++" not known\n")++
>  maybeString (not (member b agents)) 
>              ("In authentication specification, agent "++b++" not known\n")
