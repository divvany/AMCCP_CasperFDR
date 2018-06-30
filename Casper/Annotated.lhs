Type worked upon by the code generator

Export everything so omit the export section

>module Annotated

>where

>import Atoms
>import Types
>import Messages

Define annotated types of protocol message and protocol description

>type ProtMsgDesc' = 
>  (AssignmentList, MsgNo, Player, Player, Msg, Test, [VarName], [VarName])
>type ProtDesc' = [ProtMsgDesc']

The element (asss, n, Agent a, Agent b, m, t, ses, res) represents the
protocol step

  (asss)
  n. a -> b : m
  [t]

where a has extras ses, and b has extras res.

-------------------------------------------------------------------------

>type AuthSignal = ((MsgNo,AgentId),(MsgNo,AgentId),[VarName])

Each tuple contains 3 elements: 
	- Signal.Running info (MessageNr, AgentId);
	- Signal.Commit info (MessageNr, AgentId);
	- list of required variables for the auth. spec.

>type SecretSignal = (MsgNo, AgentId, Msg, [AgentId])

(n,id,sec,ls) corresponds to a secrecy spec (id,sec,ls); n is the message
number for the signal event

>type ExtraInfo = (MsgNo,AgentId,[VarName])

Each element of extra info is of the form (n, a, ls).  It represents that
agent a needs to include the extras ls in message number n.

>type AuthSpec = (Int,Auth,AuthSignal)

>type AuthInfo = (Int, Auth, AuthSignal)

----------------------------------------------------------------------
See UnboundParallel.lhs

(sender,sent conclusion,received premisses,sent premiss,test,message number)

>type SentRep = [(Player,Msg,[Msg],[Msg],String,MsgNo)] 

----------------------------------------------------------------------
Flags are options in the program, such as unboundedParallel, generateSystem etc

>data Flag = 
>   UnboundedParallel | Withdraw | TimestampsUsed 
>   | TimeUsed | TimedAuth | GuessablesUsed | CrackablesUsed | TimedCracking
>   deriving (Show, Eq)

----------------------------------------------------------------------
See http://www.haskell.org/tutorial/moretypes.html for interesting things that
can be done with this

>data Annotated = 
>   Annotated {
>       fvts                :: VarTypeList,
>       fnts                :: FnTypeList,
>       fiks                :: InverseKeyList,
>       dtdefs              :: [DataTypeDef],
>       procs               :: ProcessList,
>       protdesc            :: ProtDesc',
>       secrets             :: Secrets,
>       auths               :: Auths,
>       actvts              :: ActVarTypeList,
>       iks                 :: InverseKeyList,
>       timestampinfo       :: TimeStampInfo,
>       inlines             :: FunctionList,
>       actualAgents        :: ActualAgents,
>       intruderId          :: IntruderId,
>       intruderInitKnows   :: IntruderInitKnowledge,
>       intruderProcs       :: [ProcessName],           -- TODO: do we need
>       crackables          :: [CrackInfo],
>       deductions          :: [Deduction],
>       guessables          :: [TypeName],
>       equivs              :: [Equivalence],
>       channels            :: ChannelInfo,
>       newchannels         :: [NewChannelInfo],
>       sessinfo            :: [SessionInfo],
>       authsignals         :: [AuthSignal],
>       secretsignals       :: [SecretSignal],
>       extrainfo           :: [ExtraInfo],
>       sentrep             :: SentRep,
>       authinfo            :: [AuthInfo],
>       temporalSpecs       :: [TemporalLogicSpec],
>       flags               :: [Flag]
>   }

The components are:
    VarTypeList: The list of free variables used in the protocol
    description, with their types;
    FnTypeList: List of function names with their types;
    InverseKeyList: The list of key inverses for keys used in the protocol
    description;
    [DataTypeDef] List of definitions of user-defined datatypes
    ProcessList: The list of process names and arguments for agents
    appearing in the protocol description;
    ProtDesc: The protocol description itself;
    Secrets: The secret specifications that the protocol is supposed to
    meet;
    Auths: The authentication specifications that the protocol is supposed
    to meet;
    ActVarTypeList: The list of actual variables;
    InverseKeyList: The list of inverses for actual keys;
    TimeStampInfo: Information about how time is used in the system
    FunctionList: A list of function definitions;
    ActualAgents: The actual agents taking part in the system;
    IntruderId: The identity of the intruder
    IntruderInitKnowledge: The initial knowledge of the intruder;
    IntruderProcesses = [ProcessName]: list of processes declared as internal
    processes
    [CrackInfo]: information about crackables
    [Deduction]: The list of extra deductions.
    guessables :: [TypeName] list of guessable types
    [Equivalence]: definition of equivalences
    ChannelInfo : info about whether channels are secret or authenticated
    [AuthSignal]: info about signal events for authentication spec checking
    [SecretSignal]: info about signal events for secret spec checking
    [ExtraInfo]: info for extras fields in events
    [Flag]: List of options

----------------------------------------------------------------------
Operations on Annotated

>hasFlag :: Annotated -> Flag -> Bool
>hasFlag an f = elem f (flags an)

>addFlag :: Annotated -> Flag -> Annotated
>addFlag an f = an{flags = f:flags an}

>addFlags :: Annotated -> [Flag] -> Annotated
>addFlags an fs = an{flags = fs++flags an}

TODO Used in: channels.lhs only at the moment - should move

>actvtsnames :: Annotated -> [VarName]
>actvtsnames = map (\(a,_,_,_) -> a) . actvts

------------ TODO

Below are functions that are lifted from other types to Annotated

----------------------------------------------------------------------

>findtype :: Annotated -> VarName -> TypeName
>findtype an = findtype_ (fvts an)

>findtypeT :: Annotated -> VarName -> TypeName
>findtypeT an = findtypeT_ (fvts an)

>allOfType :: Annotated -> TypeName -> [VarName]
>allOfType = allOfType_ . map (\(a,b,_,c) -> (a,b,c)) . actvts 

>allTypes :: Annotated -> VarName -> [TypeName]
>allTypes an = allTypes_ (fvts an)

>findsubtypes :: Annotated -> VarName -> [Subtype]
>findsubtypes an = findsubtypes_ (fvts an)

>allofSubtypeTypeStatus :: Annotated -> VarName -> [Subtype] -> Status -> [VarName]
>allofSubtypeTypeStatus an = allofSubtypeTypeStatus_ (actvts an)

>makeVarGens :: Annotated -> [VarField] -> [String]
>makeVarGens an = makeVarGens_ (fvts an) (fnts an) (dtdefs an)

>showMsg :: Annotated -> Msg -> String
>showMsg an = showMsg_ (fvts an) (fnts an)

>showSenderMsg :: Annotated -> Msg -> String
>showSenderMsg an = showSenderMsg_ (fvts an) (fnts an)

>showReceiverMsg :: Annotated -> Msg -> String
>showReceiverMsg an = showReceiverMsg_ (fvts an) (fnts an) (fiks an)

>typeSet :: Annotated -> VarName -> Msg -> String
>typeSet an = typeSet_ (fvts an) (fnts an) (dtdefs an)

>typeSetNoGarbage :: Annotated -> VarName -> Msg -> String
>typeSetNoGarbage an = typeSetNoGarbage_ (fvts an) (fnts an) (dtdefs an)

>secTypeSet :: Annotated -> Msg -> String
>secTypeSet an = secTypeSet_ (fvts an) (fnts an) (dtdefs an)

----------------------------------------------------------------------
Flag Utility Methods

Output the string s only if the flag is in flags

>ifFlagString :: Annotated -> Flag -> String -> String
>ifFlagString an f s = if hasFlag an f then s else ""

>ifNotFlagString :: Annotated -> Flag -> String -> String
>ifNotFlagString an f s = if not (hasFlag an f) then s else ""

>ifAllFlagsString :: Annotated -> [Flag] -> String -> String
>ifAllFlagsString an fs s = if and (map (hasFlag an) fs) then s else ""
