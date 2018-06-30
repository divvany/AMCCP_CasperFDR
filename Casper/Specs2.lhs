Stuff used in both secrecy specs and authentication specs

>module Specs2(convert, extra, makeVarGensRM, declareRenamedTypes)
>where

>import Pprint
>import Types
>import Atoms
>import Messages
>import Useful
>import Annotated

>convert (Agent a) = a

>extra :: Annotated -> MsgNo -> AgentId -> [VarName]
>extra an n id = if extras==[] then [] else head extras
>   where extras = [ms | (nr,a,ms) <- extrainfo an, nr==n, a==id]   

>makeVarGensRM :: Annotated -> [VarField] -> [String]
>makeVarGensRM an args = 
>  filter (/= "") (map (makeVarGenRM an) args)

>makeVarGenRM :: Annotated -> VarField -> String
>makeVarGenRM an (Simple v) = 
>  let dtcons0 = [cons | (_,pats,_) <- dtdefs an, (cons,[]) <- pats]
>  in
>  if member v dtcons0  -- if v is a datatype constructor...
>  then ""              -- then produce no generator
>  else 
>    let t = findtypeT an v
>    in if t == "TS" then "Timestamp."++v++" <- TimeStamp_renamed_"
>  -- else if take 10 v == "Timestamp." then drop 10 v++" <- TS"
>       else v++" <- "++t ++"_renamed_"
>makeVarGenRM an (Subst v m) = 
>  v++" <- ALGEBRA_M::applyRenamingToSet("++typeSet an v m++")"

>declareRenamedTypes :: [TypeName] -> String
>declareRenamedTypes [] = ""
>declareRenamedTypes ts =
>  "    let "++
>  format 8 "" 
>    [t++"_renamed_ = ALGEBRA_M::applyRenamingToSet("++t++")" | t <- ts]++
>  "\n    within\n"

