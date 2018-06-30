Produce output

>module Compile (makeOutput) where

>import Useful
>import Pprint
>import Atoms
>import Messages
>import Types
>import Annotated
>import MessageTypes

Parts of output are delegated to other files

>import Channels
>import Agents
>import Algebra
>import ShowAlgebra
>import Cracking
>import Intruder
>import System
>import SecretSpecs
>import Specs
>import SecureChannels
>import TemporalLogicSpecs

>makeOutput :: String -> String -> Annotated -> String
>makeOutput conts version an =  
>   let
>       ss = [s | Sec _ s _ <- secrets an] ++ [s | StrongSec _ s _ <- secrets an]
>       secretsTypes = remdups (map (secTypeSet an) ss)
>       (fact1,laws,allfvts) = makeFactsAndLaws an
>       sessids = sessionids (sessinfo an) (procs an) (protdesc an) (actualAgents an)
>   in
>       "-- CSP script produced using Casper version "++version++"\n\n"++
>       flatmap (\l -> "-- "++l++"\n") (lines conts) ++"\n" ++
>       heading "Types" ++
>           typedefs an ++
>           produceFunctions (fnts an) (dtdefs an) (inlines an) ++
>           produceInverses (fnts an) (fiks an) (dtdefs an) (inlines an) (iks an) ++
>          "-- Types in system\n\n" ++ 
>           declareTypes an ++"\n"++
>       heading "Messages" ++ 
>           channeldefs an sessids++ 
>           "-- Roles of agents\n\n"++
>           "datatype ROLE = "++termConcat([name ++ "_role" | (_,name,_,_,_) <- procs an]) ++ 
>           "\n\n" ++
>           "HONEST_ROLE = ROLE\n\n"++
>           "-- Secrets in the protocol\n\n"++
>           "ALL_SECRETS_0 = "++ makeUnion 2 secretsTypes ++
>           "ALL_SECRETS = addGarbage_(ALGEBRA_M::applyRenamingToSet(ALL_SECRETS_0))\n\n"++
>           declareSignals an ++
>           (ifFlagString an TimeUsed timingDefs) ++
>           showFacts an allfvts fact1++
>           "external relational_inverse_image\n"++
>           "external relational_image\n"++
>           "transparent chase\n"++
>           "transparent sbisim\n\n"++
>       heading "Honest Agents"++
>           "module SYSTEM_M\n\n"++
>           messageIntTypes an++
>           processDefs an sessids++
>           produceActualAgents an++
>           "exports\n\n"++
>           messageExtTypes an++
>           messageTypesExported an++
>           produceActualSystem0 an++
>           "endmodule\n\n"++
>       heading "Algebra"++
>           "module ALGEBRA_M\n\n"++
>           showLaws an allfvts laws++
>           "exports\n\n"++
>           makeFactsAndLawsExports an++
>           "endmodule\n\n"++
>       printKCManagers an++
>       heading "The Intruder" ++ 
>           "module INTRUDER_M\n\n"++
>           produceIntruder an++
>           "exports\n\n"++
>           produceIntruderExports an++
>           produceActualSystem an++
>       heading "Specifications and Assertions"++ 
>           makeSecretSpecs an ++
>           makeSpecs an++
>           makeTemporalSpecs an

============================================================================
Declare types of actual variables

>declareTypes an  =
>  let allDataTypes = [dt | (dt,_,_) <- dtdefs an]
>      allSymTypes = 
>        [(findFnRanType (fnts an) f, f) | (f, Symb _ _) <- fnts an, 
>             not (member (findFnRanType (fnts an) f) allDataTypes)] -- ?? 
>  in 
>     showTypes (
>       [(t, "{"++commaConcat ([v | (v,t',_,_) <- (actvts an), t==t'])++ "}") | 
>           t <- remdups (map (\(_,b,_,_) -> b) (actvts an))]          -- enumerated types
>       ++
>       [(t, showRange (fnts an) f) | (t,f) <- allSymTypes]) -- symbolic DTs
>     ++ "\n" ++
>     flatmap (showdt allDataTypes) (dtdefs an)

>showTypes [] = ""
>showTypes ((t,f):tfs) =
>  let fs = f : (map snd . filter ((== t) . fst)) tfs
>      others = filter ((/= t) . fst) tfs
>  in t++" = "++makeUnion 2 fs++
>     showTypes others

showSymTypes fnts [] = ""
showSymTypes fnts ((t,f):tfs) =
  let fs = f : (map snd . filter ((== t) . fst)) tfs
      others = filter ((/= t) . fst) tfs
  in t++" = "++makeUnion 2 (map (showRange fnts) fs)++
     showSymTypes fnts others

>showRange fnts f = 
>  let domts = findFnDomType fnts f
>      arity = length domts
>      arg n = "arg_"++show n++"_"
>  in
>  "{"++f++"("++commaConcat (map arg [1..arity])++")"++
>  " | "++
>  commaConcat [arg n++" <- "++argt | (n,argt) <- zip [1..arity] domts]++
>  "}"

>showdt :: [TypeName] -> DataTypeDef -> String
>showdt dts (dt, pats, n) = 
>  funname dt++"(n_) =\n"++
>  "  if n_==0 then {"++commaConcat [cons | (cons,[]) <- pats]++"}\n"++
>  "  else "++
>  makeUnion 4 [makedtpat dts cons args | (cons,args) <- pats]++ -- "\n"++
>  dt++" = "++funname dt++"("++show n++")\n\n"

>makedtpat _ cons [] = "{"++cons++"}"
>makedtpat dts cons args = 
>  "{"++cons++"("++commaConcat["arg_"++show n | n <- [1..length args]]++")"++
>  " | "++
>  commaConcat
>    ["arg_"++show n++" <- "++
>     if member arg dts then funname arg++"(n_-1)" else arg | 
>       (arg,n) <- zip args [1..]] ++
>  "}"

============================================================================
Produce function definitions, including inverse, and sytactic sugar for 
symbolic functions and hash functions

>produceInverses fnts fiks dtdefs inlines iks = 
>  let dtcons = [cons | (_,args,_) <- dtdefs, (cons,_:_) <- args]
>      dtcons0 = [cons | (_,args,_) <- dtdefs, (cons,[]) <- args]
>  in
>  "-- Inverses of functions\n\n"++
>  -- "fiks: "++show fiks++"\n"++"dtcons: "++show dtcons++"\n"++
>  concat
>   (["inverse(" ++ k ++ ") = " ++ k' ++ "\n" | (k,k') <- iks] ++
>    ["inverse(" ++ k ++ ") = " ++ k' ++ "\n" | (k',k) <- iks, k /= k'] ++
>    remdups [makeFunctionInverse inlines (f,g) | (f,g) <- fiks, isFn fnts f]++
>    remdups [mkinverses (funname f++".arg_") (funname g++".arg_")  | 
>                 (f,g) <- fiks, member f dtcons] ++
>    remdups [mkinverses (funname f) (funname g) |
>               (f,g) <- fiks, member f dtcons0])
>  ++ "\n"

>makeFunctionInverse inlines (f,g) =
>  --let ats = findFnDomType fnts f
>  --    rant = findFnRanType fnts f
>     (concat . remdups)
>       [mkinverses frhs grhs  | 
>          Defined (f',fas,frhs) <- inlines, f==f', 
>          Defined (g',gas,grhs) <- inlines, g==g' && fas == gas]
>     ++
>     concat
>       [mkinverses (funname f++".arg_") (funname g++".arg_")  | 
>          Symbolic f' <- inlines, f==f', Symbolic g' <- inlines, g==g']

>mkinverses rhs1 rhs2 =
>  if rhs1==rhs2 then mkinverse rhs1 rhs2
>  else mkinverse rhs1 rhs2++mkinverse rhs2 rhs1
>  where mkinverse rhs1 rhs2 = 
>          "inverse("++produceFnRHS rhs1++") = "++produceFnRHS rhs2++"\n"

Produce definitions of functions
 
>produceFunctions :: FnTypeList -> DataTypeDefs -> FunctionList -> String
>produceFunctions fnts dtdefs inlines = 
>  let dtlines0 = -- definitions for user datatype constructors 
>                 -- of zero arity
>        concat [cons++" = "++funname cons++"\n" |
>                 (_,pats,_) <- dtdefs, (cons,[]) <- pats]
>      dtlinesn = -- definitions for user datatype constructors 
>                 -- of non-zero arity
>        concat [dummydef cons (length args) |
>                 (_,pats,_) <- dtdefs, (cons,args) <- pats, args/=[]]
>  in
>  "-- Definitions of user supplied functions\n\n"++
>  flatmap (produceFn fnts) inlines ++
>  (if dtlines0=="" then "" else dtlines0++"\n")++
>  dtlinesn++"\n"
  

>produceFn _ (Defined (f, args, rhs)) = 
>  produceFnLHS f args++produceFnRHS rhs++"\n"
>produceFn fnts (Symbolic f) = dummydef f (length (findFnDomType fnts f))
>produceFn _ (Inline (f, args, rhs)) =
>  produceFnLHS f args++produceFnRHS rhs++"\n"

Define f__ as synonym for f

>dummydef f arity =
>  let args = map (\n -> "arg_"++show n++"_") [1..arity]
>  in produceFnLHS f args++funname f++".("++commaConcat args++")\n"

Produce LHS of function definition for f(args)

>produceFnLHS f args = f++"("++commaConcat args++") = "

Produce RHS of function definition; hook for future extension.

>produceFnRHS rhs = rhs

------------------------------------------------------

