Produce parameterized authentication specs

>module Specs1(
>  makeAuthSpec, makeAuthSpec_UP,
>  authSpecName0, alphaAuthName0, 
>  procName, roleName
>  ) 
>where

>import Useful
>import Pprint
>import Atoms
>import Types
>import Annotated

Find name of process represented by agent a in protdesc

>procName an a = hd [pname' | (a',pname',_,_,_) <- procs an, a==a']
>roleName an a = procName an a ++ "_role"

=========================================================================

Print name(and alphabet) of parameterized process representing authentication
specification for agent taking role a, to all agents taking role b, with
authentication type at

>authSpecName0 an (a,b,at) =
>  "Authenticate"++procName an a++"To"++procName an b++show at++"_0"

>alphaAuthName0 an (a,b,at) = 
>  "Alpha"++authSpecName0 an (a,b,at)

=========================================================================

Make (parameterized) authentication spec for agents taking role represented by
a to agents taking role represented by b with authentication type at

>makeAuthSpec :: Annotated -> AuthSpec -> Output
>makeAuthSpec an (n,(a,b,at),sig) =
>  "  "++authSpecName0 an (a,b,at) ++ "(" ++ a ++ ") =\n" ++
>  makeAuthSpecRHS an (n,(a,b,at),sig) ++ "\n\n" ++
>  "  "++alphaAuthName0 an (a,b,at) ++ "(" ++ a ++ ") =\n" ++
>  makeAlphaAuthRHS an (n,(a,b,at),sig) ++ "\n\n"

=========================================================================
Make RHS of auth spec

>makeAuthSpecRHS :: Annotated -> AuthSpec -> Output
>makeAuthSpecRHS an (n,(a,b,Aliveness),_) =
>  "    signal.Running"++show n++"?"++a++"_role_!"++a++"?C_ ->\n" ++
>  "    CHAOS({signal.Commit"++show n++"."++roleName an b++"."++
>             b++"."++a++" | "++b++" <- "++findtype an b++"})"
>
>makeAuthSpecRHS an (n,(a,b,WeakAgreement),_) =
>  "    signal.Running"++show n++"?"++a++"_role_!"++a++"?"++b++" ->\n" ++
>  "    CHAOS({signal.Commit"++show n++"."++roleName an b++"."++
>             b++"."++a++"})"
>
>makeAuthSpecRHS an (n,(a,b,NonInjectiveAgreement ds),_) =
>  "    signal.Running"++show n++"."++roleName an a++"."++a++"?"++b++
>           flatmap ('?' :) ds++" ->\n" ++
>  "    CHAOS({signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++
>           flatmap ('.' :) ds++"})"
>
>makeAuthSpecRHS an (n,(a,b,Agreement ds),_) =
>  "    signal.Running"++show n++"."++roleName an a++"."++a++"?"++b++
>           flatmap ('?' :) ds++" ->\n" ++
>  "    signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++
>           flatmap ('.' :) ds++" -> STOP"
>makeAuthSpecRHS an (n,(a,b,TimedAliveness t),_) =
>  "    addTime(\n"++
>  "      signal.Running"++show n++"?"++a++"_role_!"++a++"?C_ ->\n" ++
>  "      CHAOS({signal.Commit"++show n++"."++roleName an b++"."++
>             b++"."++a++" | "++b++" <- "++findtype an b++"}),\n      "++
>  show t++")"
>
>makeAuthSpecRHS an (n,(a,b,TimedWeakAgreement t),_) =
>  "    addTime(\n"++
>  "      signal.Running"++show n++"?"++a++"_role_!"++a++"?"++b++" ->\n" ++
>  "      CHAOS({signal.Commit"++show n++"."++roleName an b++"."++
>             b++"."++a++"}),\n      "++
>  show t++")"
>
>makeAuthSpecRHS an (n,(a,b,TimedNonInjectiveAgreement t ds),_) =
>  "    addTime(\n"++
>  "    signal.Running"++show n++"."++roleName an a++"."++a++"?"++b++
>           flatmap ('?' :) ds++" ->\n" ++
>  "    CHAOS({signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++
>           flatmap ('.' :) ds++"}),\n      "++
>  show t++")"
>
>makeAuthSpecRHS an (n,(a,b,TimedAgreement t ds),_) =
>  "    addTime(\n"++
>  "      signal.Running"++show n++"."++roleName an a++"."++a++"?"++b++
>           flatmap ('?' :) ds++" ->\n" ++
>  "      signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++
>           flatmap ('.' :) ds++" -> STOP,\n      " ++
>  show t++")"
>
>makeAuthSpecRHS _ (_,(_,_,at),_) = 
>  "    STOP\n" ++
>  "  -- Authentication spec not implemented: " ++ show at

=========================================================================
Give alphabet for auth spec

>makeAlphaAuthRHS :: Annotated -> AuthSpec -> Output
>makeAlphaAuthRHS an (n,(a,b,Aliveness),_) =
>  "    {|signal.Running"++show n++"."++a++"_role_."++a++"."++b++",\n"++
>  "      signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++" |\n"++
>  "         "++b++" <- "++findtype an b++", "++a++"_role_ <- HONEST_ROLE|}"
>  -- "       "++makeGen an b++", "++a++"_role_ <- HONEST_ROLE|}"
>
>makeAlphaAuthRHS an (n,(a,b,WeakAgreement),_) =
>  "    {|signal.Running"++show n++"."++a++"_role_."++a++"."++b++",\n"++
>  "      signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++" |\n"++
>  "         "++makeGen an b++", "++a++"_role_ <- HONEST_ROLE|}"
>
>makeAlphaAuthRHS an (n,(a,b,NonInjectiveAgreement _),_) =
>  "    {|signal.Running"++show n++"."++roleName an a++"."++a++"."++b++",\n"++
>  "      signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++" |\n"++
>  "         "++makeGen an b++"|}"
>
>makeAlphaAuthRHS an (n,(a,b,Agreement _),_) =
>  "    {|signal.Running"++show n++"."++roleName an a++"."++a++"."++b++",\n"++
>  "      signal.Commit"++show n++"."++roleName an b++"."++b++"."++a++
>  " |\n"++
>  "         "++makeGen an b++"|}"
>
>makeAlphaAuthRHS an (n,(a,b,TimedAliveness _),_) =
>  "    union(\n"++
>  "      {|signal.Running"++show n++"."++a++"_role_."++a++"."++b++",\n"++
>  "        signal.Commit"++show n++"."++roleName an b++"."++
>                 b++"."++a++" |\n"++
>  "           "++makeGen an b++", "++
>               a++"_role_ <- HONEST_ROLE|},\n"++
>  "      {tock})"
>
>makeAlphaAuthRHS an (n,(a,b,TimedWeakAgreement _),_) =
>  "    union(\n"++
>  "      {|signal.Running"++show n++"."++a++"_role_."++a++"."++b++",\n"++
>  "        signal.Commit"++show n++"."++roleName an b++"."++
>                 b++"."++a++" |\n"++
>  "           "++makeGen an b++", "++
>               a++"_role_ <- HONEST_ROLE|},\n"++
>  "      {tock})"
>
>makeAlphaAuthRHS an (n,(a,b,TimedNonInjectiveAgreement _ _),_) =
>  "    union(\n"++
>  "      {|signal.Running"++show n++"."++roleName an a++"."++
>                 a++"."++b++",\n"++
>  "        signal.Commit"++show n++"."++roleName an b++"."++
>                 b++"."++a++" |\n"++
>  "           "++makeGen an b++"|},\n"++
>  "      {tock})"
>
>makeAlphaAuthRHS an (n,(a,b,TimedAgreement _ _),_) =
>  "    union(\n"++
>  "      {|signal.Running"++show n++"."++roleName an a++"."++
>                 a++"."++b++",\n"++
>  "        signal.Commit"++show n++"."++roleName an b++"."++
>                 b++"."++a++" |\n"++
>  "           "++makeGen an b++"|},\n"++
>  "      {tock})"
>
>makeAlphaAuthRHS _ _ = 
>  "    {}\n-- Not yet implemented!!"

>makeGen fvts b = b++" <- inter("++findtype fvts b++", HONEST)"

=========================================================================
AuthSpecs for Unbounded Parallel model

For unbounded parallel we do things differently; since every agent is internalised
this means that it can run a potentially unbounded number of sessions in the role a.
However, (writing n for the number of external b's) clearly there can only be n
commit events. Hence we create a parallel composition of specifications, one for
each external agent.

>makeAuthSpec_UP :: Annotated -> AuthSpec -> Output
>makeAuthSpec_UP = makeAuthSpecRHS_UP

=========================================================================
Make RHS of auth spec

>makeAuthSpecsRHS_common an n a b ds = 
>   let
>       runStr = "signal.Running"++show n++"."++roleName an a++"?"++a++
>           " : inter("++findtype an a++",HONEST)"++flatmap process (b:ds)
>           where
>               -- For signal.Running events that that are not going to be
>               -- followed by a commit event we allow the arguments to range
>               -- over any value, not just InternalUnknown ones. To see why
>               -- note that signal.Running events may occur that contain
>               -- incorrect values (because the intruder can substitute the
>               -- message) but that the honest agent would not commit to them
>               -- as it would realise the values are incorrect, but the runner
>               -- may not be able to (consider %-notation, the runner cannot
>               -- read the variables so does not know the intruder has duped
>               -- them).
>               process arg = if elem arg bVars then '!':arg else '?':arg
>       runningStr = "signal.Running"++show n++"."++roleName an a++"?"++a++
>           " : inter("++findtype an a++",HONEST)"++flatmap process (b:ds)
>           where
>               process arg =
>                   if elem arg bVars then "!"++arg
>                   -- Else, it must be an argument b receives. We only model one type
>                   -- of external agent and thus this must have come from an internal agent
>                   -- that we assume must be honest
>                   else "?"++arg++" : {"++commaConcat internalUnknownVars++"}"
>                   where
>                       typ = findtype an arg
>                       internalUnknownVars = 
>                           allofSubtypeTypeStatus an typ (findsubtypes an arg) InternalUnknown
>       commitStr = "signal.Commit"++show n++"."++roleName an b++"."++b++"."
>           ++a++flatmap ('.':) ds
>       -- bVars is the free variables in the declaration, i.e. RESPONDER(b,nb,kab) gives [b, nb,kab]
>       bVars = [v | (b',_,vars,_,_) <- procs an, v <- vars, b'==b]
>       -- the first argument to bInstance is the agent name
>       bArgsStr = commaConcat bVars
>       bInstanceTuples = zipWith (\as -> \n -> (show n):as)
>           [args | (SeqComp as) <- actualAgents an, (pn,args) <- as, pn==procName an b] [1..]
>       bInstancesTuplesStr = commaConcat (map (\ vs -> "("++commaConcat vs++")") bInstanceTuples)
>   in
>       (commitStr, runningStr, runStr, bArgsStr, bInstancesTuplesStr, -1)

>makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess runningStr 
>   runStr n bCount timedSpec timeAllowed = 
>   let
>       rest = (maybeString (bArgsStr /= "") ",")++bArgsStr
>       parallel = if timedSpec then "[| {tock} |]" else "|||"
>   in
>       "    let\n"++
>       "      bInstance("++bArgsStr++") =\n"++
>       "        "++runningStr++" ->\n"++
>       (if timedSpec then
>       "          (let\n"++
>       "            countdown(-1) = STOP\n"++
>       "            countdown(n_) = \n"++
>       "              tock -> countdown(n_-1)\n"++
>       "              [] "++commitProcess++"\n"++
>       "          within countdown("++show timeAllowed++"))\n"++
>       "      [] tock -> bInstance("++bArgsStr++")\n"
>       else
>       "          "++commitProcess++"\n"
>       )++
>       "      run("++bArgsStr++") = \n"++
>       "        "++runStr++" -> \n"++
>       "        run("++bArgsStr++")\n"++
>       "    within\n"++
>       "      -- Number argument tuples so that duplicates are not eliminated\n"++
>       "      "++parallel++" (_,"++bArgsStr++"): {"++bInstancesTuplesStr++"} @\n"++
>       "        sbisim(bInstance("++bArgsStr++")) ||| run("++bArgsStr++")"

>makeAuthSpecRHS_UP :: Annotated -> AuthSpec -> Output
>makeAuthSpecRHS_UP an (n,(a,b,Agreement ds),_) =
>   let
>       (commitStr, runningStr, runStr, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b ds
>       commitProcess = commitStr++" -> STOP"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount False 0

>makeAuthSpecRHS_UP an (n,(a,b,NonInjectiveAgreement ds),_) =
>   let
>       (commitStr, runningStr, runStr, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b ds
>       commitProcess = "RUN({"++commitStr++"})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount False 0

>makeAuthSpecRHS_UP an (n,(a,b,Aliveness),_) =
>   let
>       (_, _, _, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b []
>       runningStr = "signal.Running"++show n++"?"++a++"_role_?"++a++
>           " : inter("++findtype an a++",HONEST)"
>       runStr = runningStr
>       commitStr = "signal.Commit"++show n++"."++roleName an b++"."++b++"."++a
>       commitProcess = "RUN({"++commitStr++"})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess
>       runningStr runStr n bCount False 0

>makeAuthSpecRHS_UP an (n,(a,b,WeakAgreement),_) =
>   let
>       (_, _, _, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b []
>       runningStr = "signal.Running"++show n++"?"++a++"_role_?"++a++
>           " : inter("++findtype an a++",HONEST)!"++b
>       runStr = runningStr
>       commitStr = "signal.Commit"++show n++"."++roleName an b++"."++b++"."++a
>       commitProcess = "RUN({"++commitStr++"})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess
>       runningStr runStr n bCount False 0

>makeAuthSpecRHS_UP an (n,(a,b,TimedAgreement t ds),_) = 
>   let
>       (commitStr, runningStr, runStr, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b ds
>       commitProcess = commitStr++" -> RUN({tock})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount True t

>makeAuthSpecRHS_UP an (n,(a,b,TimedNonInjectiveAgreement t ds),_) = 
>   let
>       (commitStr, runningStr, runStr, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b ds
>       commitProcess = commitStr++" -> RUN({"++commitStr++",tock})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount True t

>makeAuthSpecRHS_UP an (n,(a,b,TimedAliveness t),_) = 
>   let
>       (_, _, _, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b []
>       runningStr = "signal.Running"++show n++"?"++a++"_role_?"++a++
>           " : inter("++findtype an a++",HONEST)"
>       runStr = runningStr
>       commitStr = "signal.Commit"++show n++"."++roleName an b++"."++b++"."++a
>       commitProcess = commitStr++" -> RUN({"++commitStr++",tock})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount True t

>makeAuthSpecRHS_UP an (n,(a,b,TimedWeakAgreement t),_) = 
>   let
>       (_, _, _, bArgsStr, bInstancesTuplesStr, bCount) = 
>           makeAuthSpecsRHS_common an n a b []
>       runningStr = "signal.Running"++show n++"?"++a++"_role_?"++a++
>           " : inter("++findtype an a++",HONEST)!"++b
>       runStr = runningStr
>       commitStr = "signal.Commit"++show n++"."++roleName an b++"."++b++"."++a
>       commitProcess = commitStr++" -> RUN({"++commitStr++",tock})"
>   in makeAuthSpecsRHS_UP_makeOutput bArgsStr bInstancesTuplesStr commitProcess 
>       runningStr runStr n bCount True t


>makeAuthSpecRHS_UP _ _ = spaces 4++" --Not yet implemented"


