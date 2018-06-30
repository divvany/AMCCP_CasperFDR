Define various atomic types: variables, typing of variables, functions, key
inverses, timestamps.

>module Atoms (
>  -- variables
>  VarName, AgentId,
>  -- types of variables
>  TypeName, VarTypeList, ActVarTypeList, 
>  findtype_, findtypeT_, findsubtypes_, allofSubtypeTypeStatus_, allOfType_, allTypes_,
>  Status(Normal,Error_Status,External,InternalKnown,InternalUnknown),
>  Subtype,
>  -- functions
>  FnType(Symb, Defed, HashFunction), 
>  FnTypeList, isFn, isHashFunction, findFnType, findFnType1, 
>  findFnDomType, findFnRanType, 
>  -- types
>  isAType,
>  -- inverses
>  InverseKeyList, inverse1, -- inverse2, 
>  -- timestamps
>  TimeStampInfo(NotUsed, MRTUsed, TimeStampsUsed), 
>  DataTypeDef, DataTypeDefs, dtAtoms, dtConss
>  )

>where

>import Useful
>import Maybe1

=========================================================================

Variable names, agent identities

>type VarName = String
>type AgentId = String

=========================================================================
Typing of variables

>type TypeName = String
>type Subtype = String

>type VarTypeList = [(VarName, TypeName, [Subtype])]

>data Status =	Normal | Error_Status | External | InternalKnown | InternalUnknown
>		deriving(Eq, Show)

>type ActVarTypeList = [(VarName, TypeName, Status, [Subtype])]

The functions below are not used directly. They are lifted to use the
Annotated datatype in Annotated.lhs.

>findtype_ :: VarTypeList -> VarName -> TypeName
>findtype_ tl v = 
>  hd ([t | (v',t,_) <- tl++nowtl, v==v' || v==v'++"_X_"] ++ ["_Internal"])

The comparison with v'++"_X_" is a hack used for generating new type names
where the same field appears in both senders-extras and receivers-extras.  It
is used in Channels.lhs and RenamedSystem.lhs

>nowtl :: VarTypeList
>nowtl = [("now", "TimeStamp", []),("Timestamp.now", "TimeStamp", [])]

>allOfType_ :: VarTypeList -> TypeName -> [VarName]
>allOfType_ tl t = sortremdups [v | (v,t',_) <- tl, t == t']

>allTypes_ :: VarTypeList -> VarName -> [TypeName]
>allTypes_ tl v = [t | (v',t, _) <- tl, v==v']

Return type, but substitute TS for TimeStamp

>findtypeT_ :: VarTypeList -> VarName -> TypeName
>findtypeT_ tl v = 
>  let t1 = findtype_ tl v 
>  in if t1=="TimeStamp" then "TS" else t1

>findsubtypes_ :: VarTypeList -> VarName -> [Subtype]
>findsubtypes_ fvts v = concat [sts | (vname,_,sts) <- fvts, vname == v]

We make the convention that if a variable had no subtypes given then it is in 
every subtype

>allofSubtypeTypeStatus_ :: ActVarTypeList -> TypeName -> [Subtype] -> Status -> [VarName]
>allofSubtypeTypeStatus_ atvs tn sts s = 
>   [var | (var, vartype, status, subtypes) <- atvs, vartype == tn, 
>           status == s, sts == [] || subtypes == [] || sts \\ subtypes /= sts]

=========================================================================
Functions

>data FnType = Symb [TypeName] TypeName |    -- symbolic functions
>              Defed [TypeName] TypeName |   -- functions with explicit def
>              HashFunction                  -- public hash functions
>              deriving (Eq, Show)
>type FnTypeList = [(VarName, FnType)]

>findFnType :: FnTypeList -> VarName -> Maybe_ FnType
>findFnType fnts f 
>  | matches == []       = Error ("Undeclared function: " ++ f ++ "\n")
>  | length matches > 1  = Error ("Multiply declared function: " ++ f ++ "\n")
>  | length matches == 1 = Yes (hd matches)
>      where matches = [t | (g,t) <- fnts, f == g]

>isHashFunction :: FnTypeList -> VarName -> Bool
>isHashFunction fnts f = findFnType1 fnts f == HashFunction

>findFnType1 :: FnTypeList -> VarName -> FnType
>findFnType1 fnts f = let Yes t = findFnType fnts f in t

>isFn :: FnTypeList -> VarName -> Bool
>isFn fnts f = 
>  case findFnType fnts f of
>    Error _ -> False
>    Yes _ -> True

>findFnDomType :: FnTypeList -> VarName -> [TypeName]
>findFnDomType fnts f = 
>  let Yes ft = findFnType fnts f
>  in 
>  case ft of
>    Symb ats _ -> ats
>    Defed ats _ -> ats

>findFnRanType :: FnTypeList -> VarName -> TypeName
>findFnRanType fnts f = 
>  let Yes ft = findFnType fnts f
>  in 
>  case ft of
>    Symb _ rt -> rt
>    Defed _ rt -> rt
>    HashFunction -> error ("findFnRanType applied to HashFunction ")


>isAType :: VarTypeList -> FnTypeList -> TypeName -> Bool
>isAType fvts fnts tn = 
>  let allTypes = map (\(_,b,_) -> b) fvts++
>                 [t | (_,Symb _ t) <- fnts]++
>                 [t | (_,Defed _ t) <- fnts]
>  in member tn allTypes

=========================================================================

Inverses of keys

>type InverseKeyList = [(VarName, VarName)]

>inverse :: InverseKeyList -> VarName -> Maybe_ VarName

>inverse fiks v 
>  | length matches == 1   = Yes (hd matches)
>  | matches == []         = Error ("Inverse not found: " ++ v ++ "\n")
>  | length matches > 1    = Error ("Multiply defined inverse: " ++ v ++ "\n")
>  where matches = [v' | (v'',v') <- fiks, v'' == v] 
>                  ++ [v' | (v',v'') <- fiks, v'' == v, v' /= v'']

>inverse1 :: InverseKeyList -> VarName -> VarName
>inverse1 fiks v = body (inverse fiks v)

>{-
>inverse2 :: InverseKeyList -> Msg -> Msg
>inverse2 fiks (Atom k) = Atom (inverse1 fiks k)
>inverse2 fiks (Apply f as) = Apply (inverse1 fiks f) as
>inverse2 fiks (Forwd v m) = inverse2 fiks m
>inverse2 fiks (Undec m v) = inverse2 fiks m
>-}


=========================================================================
Time stamp information

>data TimeStampInfo = NotUsed | MRTUsed Int | TimeStampsUsed Int Int Int
>                     deriving (Eq,Show)

* NotUsed represents that time is not used at all
* MRTUsed rt represents that each run will take at most rt time units; 
should occur only when there are timed authentications or timed key compromise 
* TimeStampsUsed t0 t1 rt represents that timestamps will take the range 
t0..t1, and each run will take at most rt time units; should occur only when
timestamps are used 

=========================================================================

Datatype definitions

>type DataTypeDef = (TypeName, [Pattern], Int)
>type Pattern = (VarName, [VarName])
>type DataTypeDefs = [DataTypeDef]

Atomic values of datatype definition

>dtAtoms :: DataTypeDef -> [VarName]
>dtAtoms (_, pats, _n) = [cons | (cons,[]) <- pats]

Constructors of datatype definition

>dtConss :: DataTypeDef -> [VarName]
>dtConss (_, pats, _) = [cons | (cons,_:_) <- pats]
