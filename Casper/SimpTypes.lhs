>module SimpTypes (
>  Simpl(RemoveFields, RemoveHashedFields, RemoveHash, RemoveEncryption,
>        SwapPairs, Coalesce, RemovePlainAndEnc),
>  Simpls,
>  SimplInput, SimplInputpd
>  )


>where

>-- import Useful
>-- import Maybe1
>import Types
>import Atoms
>import Messages

=========================================================================
Complete input

>type SimplInput = 
>  (VarTypeList, FnTypeList, InverseKeyList, [DataTypeDef], ProcessList, 
>   ProtDesc, Secrets, Auths, Simpls,
>   VarTypeList, InverseKeyList, TimeStampInfo, FunctionList, ActualAgents, 
>   IntruderId, IntruderInitKnowledge, [Deduction])

>type SimplInputpd = 
>  (VarTypeList, FnTypeList, InverseKeyList, [DataTypeDef], ProcessList, ProtDesc, 
>   Secrets, Auths, Simpls)

===========================================================================

>data Simpl = RemoveFields [TypeName]
>	    | RemoveHash Msg
>	    | RemoveEncryption Msg
>	    | SwapPairs (TypeName, TypeName)
>	    | Coalesce [TypeName]
>           | RemoveHashedFields Msg
>           | RemovePlainAndEnc
>              deriving (Eq, Show)

>type Simpls = [Simpl]


