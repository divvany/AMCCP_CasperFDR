>module TemporalLogicSpecs (makeTemporalSpecs, normalizeTemporalSpecs)
>where

>import Prelude

>import Annotated
>import Atoms
>import List(sortBy)
>import Messages
>import Pprint
>import Types
>import Useful

*******************************************************************************
Test Methods
*******************************************************************************

Imports needed only for testing methods

import Annotate
import Parse
import IO
import Maybe1

Test the temporal specs on a particular file and output the result to the 
terminal.

test :: String -> IO()
test filename =
   do
     fromHandle <- openFile (filename ++ ".spl") ReadMode 
     contents   <- hGetContents fromHandle
     putStr ((makeTemporalSpecs . annotate . body . parse) contents)

Pretty prints an automaton for quick inspection.

showAutomaton :: Automaton -> Output
showAutomaton (_,states,trans) = 
   "States =\n"++
   flatmap (\(es, _, prohib,id) -> show id++" : "++commaConcat (map (\(x,_,y,_) -> x++y) es)++" "++show prohib++"\n") states++
   "Trans =\n"++
   flatmap (\(from,to,(x,_,y,_)) -> show from++" -> "++show to++" on "++x++y++"\n") trans

Formula used for tests

f = AlwaysIf 
   (And (Does ("b",Receive,"3",["nb"])) 
       (Previously (Does ("b",Receive,"1",["na"]))))
   (Previously (And
       (Does ("a", Send,"3", ["nb"]))
       (Previously (Does ("b", Send, "2", ["nb","na"])))
    ))

*******************************************************************************
Main methods
*******************************************************************************

Annotation method for the specs. It normalizes the formulas and adds the
sender and possibly the receiver to the list of variables that are bound
by an event.

>normalizeTemporalSpecs :: VarTypeList -> ActVarTypeList -> ProtDesc' -> 
>   [TemporalLogicSpec] -> [TemporalLogicSpec]
>normalizeTemporalSpecs fvts actvts protdesc temporalSpecs = 
>       map (\ f -> bindEvents (normalize f)) temporalSpecs
>   where
>       actualVars = [v | (v,_,_,_) <- actvts]
>       bindEvents (Does (agentId,otherAgentId,parity,msgNo,varsToBind)) = 
>               Does e'
>           where
>               -- Bind agentId and otherAgentId (if needed)
>               varsToBind' = varsToBind++
>                   case parity of
>                      Send    -> subOrFreeVar sender agentId
>                                  ++subOrFreeVar recipient otherAgentId
>                      Receive -> subOrFreeVar recipient agentId
>                                  ++subOrFreeVar sender otherAgentId
>                   where
>                       subOrFreeVar (Agent freeVar) possActVar =
>                           if possActVar == "" then []
>                           else if possActVar `elem` actualVars then 
>                               [Substitution freeVar possActVar] 
>                           else [FreeVar freeVar]
>                       subOrFreeVar _ _ = []
>               e' = (agentId,otherAgentId,parity,msgNo,varsToBind')
>               (_, _, sender, recipient, _, _, _, _) = 
>                   head (filter (\(_,n,_,_,_,_,_,_) -> n == msgNo) protdesc)
>       bindEvents (And f1 f2) = And (bindEvents f1) (bindEvents f2) 
>       bindEvents (Or f1 f2) = Or (bindEvents f1) (bindEvents f2) 
>       bindEvents (AlwaysIf f1 f2) = AlwaysIf (bindEvents f1) (bindEvents f2) 
>       bindEvents (Previously f) = Previously (bindEvents f)

Output the CSP for the temporal specs

>makeTemporalSpecs :: Annotated -> Output
>makeTemporalSpecs an =
>   maybeString (temporalSpecs an /= []) (
>   heading "Temporal Specifications"++
>   "module TEMPORAL_SPEC_COMMON_M\n"++
>   "exports\n"++
>   "  -- System to be used for checking temporal specifications\n"++
>   "  SYSTEM(Renaming,AlphaSpec) =\n"++
>   "    let\n"++
>   "      FactsExcludedFromClosure = {f_ | (f_, _) <- Renaming}\n\n"++
>   "      -- Close up the intruder's initial knowledge not including any facts\n"++
>   "      -- that later get renamed in Renaming.\n"++
>   "      (IK, Deductions"++
>          (ifNotFlagString an UnboundedParallel ",KnowableFact")++
>          ") =\n"++
>   "        INTRUDER_M::CloseButNotFacts_(\n"++
>   "          ALGEBRA_M::applyRenamingToSet(INTRUDER_M::IK0),\n"++
>   "          ALGEBRA_M::applyRenamingToDeductions(INTRUDER_M::Base_Deductions),\n"++
>   "          ALGEBRA_M::applyRenamingToSet(INTRUDER_M::KnowableFact),\n"++
>   "          FactsExcludedFromClosure)\n\n"++
>   "      LearnableFact = diff("++
>           (if hasFlag an UnboundedParallel then "INTRUDER_M::KnowableFact" else "KnowableFact")++", IK)\n\n"++
>   "      -- Rename all infers as specififed by renaming\n"++
>   "      INTRUDER_0 = \n"++
>   "        INTRUDER_M::INTRUDER_00(Deductions,LearnableFact)\n"++
>   "          [[infer.ded_ <- b_ | (f_,b_) <- Renaming, (f_',fs_) @@ ded_ <- Deductions, f_' == f_]]\n"++
>   "          \\ {| infer |}\n"++
>   "    within\n"++
>   "      ((SYSTEM_M::SYSTEM_0 [| IntruderInterface |] INTRUDER_M::BUILD_INTRUDER'(INTRUDER_0,IK))\n"++
>   "      [[internalAgentSend.a_.b_.m_ <- send.a_.b_.m_\n"++
>   "        | a_ <- ALL_PRINCIPALS, b_ <- ALL_PRINCIPALS, m_ <- OUTPUT_MSG\n"++
>   "      ]]\n"++
>   "      \\ diff(Events, AlphaSpec), Deductions)\n"++
>   "endmodule\n\n"++
>   "-- Channel definitions\n"++
>   "channel internalAgentSend : ALL_PRINCIPALS.ALL_PRINCIPALS.OUTPUT_MSG\n\n"
>   )++
>   concat (zipWith (makeTemporalSpec an) (temporalSpecs an) [1..])

>makeTemporalSpec :: Annotated -> TemporalLogicSpec -> Int -> Output
>makeTemporalSpec an spec n =
>   let
>       formula = spec
>       aut = buildAutomaton an spec
>       moduleName = "TEMPORAL_SPEC_"++show n++"_M"
>   in
>       heading ("Temporal Logic Spec "++show n)++
>       "module "++moduleName++"\n"++
>       automatonToCSP an spec aut++
>       outputSystem an spec++
>       "endmodule\n\n"++
>       "assert "++moduleName++"::SPEC [T= "++moduleName++"::SYSTEM_SPEC\n\n"

*******************************************************************************
Methods on formulas
*******************************************************************************

We convert all trees of And such that the top left node is a Done (if one
exists at all). Hence (P x && (y && P z) goes to y && (P x && P y).

Furthermore we convert any formula like (Or (Previously f1 (Previously f2)) to
Previously (Or f1 f2). 

>normalize :: TLFormula -> TLFormula
>normalize (Or (Previously f1) (Previously f2)) = 
>   normalize (Previously (Or f1 f2))
>normalize (And (Does e) f2) = 
>   And (normalize (Does e)) (normalize f2)
>normalize (And f1 (Does e)) =
>   normalize (And (Does e) f1)
>normalize (And f1 f2) = 
>   case f1' of
>       Does e  -> And f1' f2'
>       x       -> case f2' of
>                   Does e  -> And f2' f1'
>                   y       -> And f1' f2'
>   where
>       f1' = normalize f1
>       f2' = normalize f2
>normalize (Or f1 f2) = Or (normalize f1) (normalize f2)
>normalize (Previously f1) = Previously (normalize f1)
>normalize (AlwaysIf f1 f2) = 
>   AlwaysIf (normalize f1) (normalize f2)
>normalize x = x

Return the list of all events that occur within a formula.

>allEvents :: TLFormula -> [TLEvent]
>allEvents (Does e) = [e]
>allEvents (Or f1 f2) = allEvents f1++allEvents f2
>allEvents (And f1 f2) = allEvents f1++allEvents f2
>allEvents (AlwaysIf f1 f2) = allEvents f1++allEvents f2
>allEvents (Previously f1) = allEvents f1

*******************************************************************************
Automaton Types and Helper Methods
*******************************************************************************

State = (List of events that have occured, Bound Variables, block state, uniqueid)

Block state is used to indicate if the top level event on the left hand side
of an implication is allowed in this state or not.

>data BlockState = Blocked | Allow TLEvent deriving (Eq, Show, Ord)

>type State = ([TLEvent], [VarName], BlockState, Int)
>type StateMap = [State]

A transition is (from,to,on event)

>type Transition = (Int, Int, TLEvent)
>type TransitionMap = [Transition]

Below, Int refers to last assigned state

>type Automaton = (Int, StateMap, TransitionMap)

If a state exists such that the events that have been performed so far are 
equal to the events supplied then return it, else return Nothing.

>maybeGetStateByEvents :: Automaton -> [TLEvent] -> Maybe State
>maybeGetStateByEvents (_,states,_) es = 
>   if poss == [] then Nothing else Just (hd poss)
>   where 
>       poss = filter (\(es'',_,_,_) -> es' == es'') states
>       es' = sortremdups es

Get the state such that the events that have been performed so far are equal
to the events supplied.

>getStateByEvents :: Automaton -> [TLEvent] -> State
>getStateByEvents aut es =
>   case maybeGetStateByEvents aut es of
>       Just st     -> st
>       Nothing     -> error ("TemporalLogicSpecs.lhs::getStateByEvents Could not fetch state: "++show es)

Get the state with the given integer id

>getStateById :: Automaton -> Int -> State
>getStateById (_,states,_) id = head (filter (\(_,_,_,id') -> id == id') states)

Find and return the state with the given events, or else create the state and
return it.

>findOrInsertState :: Automaton -> [TLEvent] -> [VarName] -> (Automaton, Int)
>findOrInsertState aut es boundVars = 
>   let
>       (next, states, trans) = aut
>       es' = sortremdups es
>       newState = (es',sortremdups boundVars, Blocked, next)
>   in
>       case maybeGetStateByEvents aut es' of
>           Just (_,_,_,id) -> (aut,id)
>           Nothing         -> ((next+1, newState:states, trans), next)

Given a state changes its block status to Allow e where e is the event
that should be allowed.

>unblockState :: Automaton -> Int -> TLEvent -> Automaton
>unblockState (next,states,trans) stid e =
>   (next,st':(states \\ [st]),trans)
>   where 
>       st' = (es,bVs,Allow e,id)
>       st = getStateById (next,states,trans) stid
>       (es,bVs,Blocked,id) = st

Insert a transition between the two numbered states on the given event.

>insertTransition :: Automaton -> Int -> Int -> TLEvent -> Automaton
>insertTransition (next,states,trans) idFrom idTo ev = 
>   (next, states, remdups ((idFrom,idTo,ev):trans))

Get all immediate outgoing transitions from the given state (i.e. 1 step of
transitions)

>getTransitionsFromState :: Automaton -> Int -> [Transition]
>getTransitionsFromState (next, states, trans) stid = 
>   filter (\(from,_,_) -> from == stid) trans

Get immediate succesor states (i.e. states at most 1 transition away).

>getNextStatesFromState :: Automaton -> Int -> [Int]
>getNextStatesFromState aut stid = 
>   map (\(_,toId,_) -> toId) (getTransitionsFromState aut stid)

Get all paths of states that are reachable from the given state.

>getReachablePathsFromState :: Automaton -> Int -> [[Int]]
>getReachablePathsFromState aut stid =
>   if sts == [] then [[stid]]
>   else [stid:paths | st' <- sts, paths <- getReachablePathsFromState aut st']
>   where
>       sts = getNextStatesFromState aut stid

Get all paths of states that are reachable from the given state and whose last
state is in the set of states given.

>getReachableStatesEndingAtStates :: Automaton -> Int -> [Int] -> [Int]
>getReachableStatesEndingAtStates aut stid sts = 
>   (remdups . concat . filter (\path -> last path `elem` sts)) 
>       (getReachablePathsFromState aut stid)

Get all transitions that are reachable from the given state such that the last
state they visit is in the set of states given.

>getReachableTransitionsEndingAtStates :: Automaton -> Int -> [Int] -> [Transition]
>getReachableTransitionsEndingAtStates aut stid sts =
>   concat [getTrans path | path <- getReachablePathsFromState aut stid, last path `elem` sts]
>   where 
>       (_,_,trans) = aut      
>       getTrans (st1id:st2id:sts) = 
>               [(idF,idT,e) | (idF,idT,e) <- trans, idF==st1id, idT==st2id]
>               ++ getTrans (st2id:sts)
>       getTrans x = []

Extracts the top level event from a formula. For example, if the spec is
if e1 then previously e2 it would return e1.

>extractEvent :: TLFormula -> TLFormula
>extractEvent (AlwaysIf f1 f2) = extractEvent f1
>extractEvent (And a b) = extractEvent a
>extractEvent a = a

Construct a product automata for f1 and f2.

Given an automaton and two formulas (along with the list of states tha automaton
is currently in) it extends the automaton with an automaton that allows f1 and
f2 to be verified in a parallel manner. This is done by taking the cross product
of the states used to verify f1 and the states used to verify f2.

It returns a tuple:

    (aut', (f1states,currs1), (f2states,currs2))
  
where aut' is the new automaton, f1states is the set of states that are used for
verifying f1, currs1 is the set of states that the automaton is in after (just)
verifying f1. For examples of how to use these see (and compare) the construction
of currs' in the And and Or cases of extendAutomaton.

>constructCombinedAutomaton :: Annotated -> Automaton -> TLFormula -> 
>   TLFormula -> [Int] -> (Automaton, ([Int], [Int]), ([Int], [Int]))
>constructCombinedAutomaton an aut f1 f2 currs = 
>   let
>       -- Construct the automata for f1
>       (aut1, currs1) = extendAutomaton an currs f1 aut 
>       f1states = concat [getReachableStatesEndingAtStates aut1 st currs1 | st <- currs]
>       f1trans = concat [getReachableTransitionsEndingAtStates aut1 st currs1 | st <- currs]
>       -- We then construct the automata for f2
>       (aut2, currs2) = extendAutomaton an currs f2 aut1
>       f2states = concat [getReachableStatesEndingAtStates aut2 st currs2 | st <- currs]
>       f2trans = concat [getReachableTransitionsEndingAtStates aut2 st currs2 | st <- currs]
>       -- We now have an automata that can do f1 || f2 from currs. We now
>       -- convert it by taking the cross product of the new states
>       aut' = foldr addTrans (foldr addStates aut2 f1states) f1states
>           where
>               addStates f1st aut = foldr (addStates' f1st) aut f2states
>               addStates' f1st f2st aut = fst (findOrInsertCombinedState aut f1st f2st)
>               findOrInsertCombinedState aut st1 st2 = 
>                   let (es1,bVs1,_,_) = getStateById aut st1
>                       (es2,bVs2,_,_) = getStateById aut st2
>                   in findOrInsertState aut (es1++es2) (bVs1++bVs2)

>               addTrans f1st aut = foldr (addTrans' f1st) aut f2states
>               addTrans' f1st f2st aut = 
>                   let
>                       (es1,_,_,_) = getStateById aut f1st
>                       (es2,_,_,_) = getStateById aut f2st
>                       stid = getCombinedState aut f1st f2st
>                       f (_,_,e) aut = insertTransition aut stid idTo e
>                           where (_,_,_,idTo) = getStateByEvents aut (e:es1++es2)
>                   in
>                       foldr f aut (
>                           -- For every transition that is a transition from
>                           -- f1st add a transition from the combined state
>                           -- (ditto for f2st).
>                           intersection (getTransitionsFromState aut1 f1st) f1trans
>                           ++ intersection (getTransitionsFromState aut2 f2st) f2trans)
>       getCombinedState aut id1 id2 = 
>           let
>               (es1,_,_,_) = getStateById aut id1
>               (es2,_,_,_) = getStateById aut id2
>               (_,_,_,stid) = getStateByEvents aut (es1++es2)
>           in stid
>   in
>       (aut', (f1states, currs1), (f2states, currs2))

*******************************************************************************
Automaton Construction
*******************************************************************************

Produces an automaton from a temporal logic specification

>buildAutomaton :: Annotated -> TemporalLogicSpec -> Automaton
>buildAutomaton an f = 
>       fst (extendAutomaton an [0] f (1, [startState], []))
>   where
>       startState = ([],boundVars,Blocked,0)
>       -- If the agentId of the event that is blocked initially is an
>       -- actual variable then no variables are bound initially,
>       -- otherwise the agentId is bound initially as we create one
>       -- instance of STATE_0 for each possible value of agentId (and
>       -- then interleave them). See the Automaton to CSP conversion
>       -- section below for a more detailed explanation.
>       boundVars = if agentId `elem` [v | (v,_,_,_) <- actvts an] then [] else [agentId]
>       Does (agentId,_,_,_,_) = extractEvent f

Function that does all the work building the automaton. It takes an arugment
that gives the current automaton that has been built, along with all the states
that the automaton is currently in. The method then recurses on the structure
of the formula given returning the automaton that satisfies the formula and
the list of states that are its final states.

Arguments :
    currs is a list of the states that we are currently in
    aut is the current automaton

>extendAutomaton :: Annotated -> [Int] -> TLFormula -> Automaton -> 
>   (Automaton, [Int])

This should only occur once at the top level of the automaton, if not then
the formula is malformed.

>extendAutomaton an currs (AlwaysIf (Does e) f2) aut =
>   let
>       (aut', endStates) = extendAutomaton an currs f2 aut
>       aut'' = foldr unblock aut' endStates
>           where unblock st aut = unblockState aut st e
>   in (aut'', endStates)

The normalize method above ensures that the Does e event is always at the top
left of the And tree in the formula.

>extendAutomaton an currs (AlwaysIf (And (Does e) f1) f2) aut =
>   let
>       (aut',(f1states,currs1),(f2states,currs2)) = 
>           constructCombinedAutomaton an aut f1 f2 currs
>       getCombinedState aut id1 id2 = 
>           let
>               (es1,_,_,_) = getStateById aut id1
>               (es2,_,_,_) = getStateById aut id2
>               (_,_,_,stid) = getStateByEvents aut (es1++es2)
>           in stid
>       -- We allow e to occur in any state where f1 has not occured, or in any
>       -- state where f1 and f2 have occured.
>       statesToUnblock = 
>           [getCombinedState aut' id1 id2 | id1 <- f1states \\ currs1, id2 <- f2states]
>           ++endStates
>       endStates = 
>           [getCombinedState aut' id1 id2 | id1 <- currs1, id2 <- currs2]
>       aut'' = foldr unblock aut' statesToUnblock
>           where unblock st aut = unblockState aut st e
>   in (aut'', endStates)

Construction: for every state that we are currently in a new state is added
and a transition on an e is then added between the two states.

>extendAutomaton an currs (Does e) aut =
>   let 
>       addStateAndTransition stId (aut,states) = 
>           let (aut', newState) = findOrInsertState aut (e:es) (bVs++[v | FreeVar v <- bVsNew])
>               (es,bVs,_,_) = getStateById aut stId
>               (a,_,_,_,bVsNew) = e
>           in (insertTransition aut' stId newState e, newState:states)
>   -- Add a new state and transition from every state in curr in a new
>   -- state where e has occured
>   in foldr addStateAndTransition (aut, []) currs

Case below: f2 is run then afterwards an e is allowed. The normalize method
prevents us from having to do the symmetric case to this.

>extendAutomaton an currs (And (Does e) f2) aut = 
>   let
>       (aut1, news1) = extendAutomaton an currs f2 aut
>       (aut2, news2) = extendAutomaton an news1 (Does e) aut1
>   in (aut2, news2)

Case below is the most complicated case. It constructs a combined automata
for f1 and f2 and then returns as the current states any state <s1++s2> where
s1 is in the ending states for the verification of f1 and s2 is in the ending
states for the verification of f2.

Transitions are then added in the obvious way.

>extendAutomaton an currs (And f1 f2) aut = 
>   let
>       (aut',(f1states,currs1),(f2states,currs2)) = 
>           constructCombinedAutomaton an aut f1 f2 currs
>       getCombinedState aut id1 id2 = 
>           let
>               (es1,_,_,_) = getStateById aut id1
>               (es2,_,_,_) = getStateById aut id2
>               (_,_,_,stid) = getStateByEvents aut (es1++es2)
>           in stid
>       currs' = 
>           [getCombinedState aut' id1 id2 | id1 <- currs1, id2 <- currs2]
>   in (aut', currs')

For the case below we create an automaton identical to the one in the And case
with the exception of the ending states. Instead of ending in the state where
both f1 and f2 are satisfied we end in any state where either f1 or f2 is 
satisfied. This is done by returning as the current states any state <s1++s2>
where either s1 is an accepting state for f1 or s2 is an accepting state for f2.

>extendAutomaton an currs (Or f1 f2) aut = 
>   let
>       (aut',(f1states,currs1),(f2states,currs2)) = 
>           constructCombinedAutomaton an aut f1 f2 currs
>       getCombinedState aut id1 id2 = 
>           let
>               (es1,_,_,_) = getStateById aut id1
>               (es2,_,_,_) = getStateById aut id2
>               (_,_,_,stid) = getStateByEvents aut (es1++es2)
>           in stid
>       currs' = 
>           [getCombinedState aut' id1 id2 | id1 <- currs1, id2 <- f2states]
>           ++[getCombinedState aut' id1 id2 | id1 <- f1states, id2 <- currs2]
>   in (aut', currs')

Because of the way we restrict the syntax the previously is taken to 
be implicit and thus can be traversed through.

>extendAutomaton an currs (Previously f1) aut = 
>   extendAutomaton an currs f1 aut


*******************************************************************************
Automaton to CSP Conversion
*******************************************************************************

The main process is called SPEC. Within SPEC a process is declared for
each state in the automaton and the arguments to it are the variables
that have been bound up to this state. The overall goal is to have an
interleaving of the STATE_0 processes; in particular one process is
created for each external agent of the correct type. For example, if the
spec was "if agent a sends...." and there were two external instances of
agent a (say with ids Bob and Alice the overall SPEC would equal
STATE_0(Alice) ||| STATE_0(Bob)).

>automatonToCSP :: Annotated -> TemporalLogicSpec -> Automaton -> Output
>automatonToCSP an formula (next, states, trans) =
>   let
>       aut' = (next, sortBy stateComp states, trans)
>       stateComp (_,_,_,id1) (_,_,_,id2) = compare id1 id2
>       Does ev = extractEvent formula
>       -- The agentid (i.e. "a") of the process whose behaviour the temporal
>       -- formula is attempting to restrict.
>       (agentId,_,_,_,_) = ev
>       agentProcName = hd [pname' | (a',pname',_,_,_) <- procs an, agentId==a']
>       agentsToCheck = [name | (SeqComp as) <- actualAgents an, (pn,name:_) <- as, 
>                               pn == agentProcName]
>       interleave ps = foldr1 (\p1 -> \p2 -> p1++" ||| "++p2) ps
>   in
>       "  -- The set of all events that we are interested in\n"++
>       "  AlphaSpec = "++
>       makeUnion 4 [makeEventSet an e [] 8 | e <- allEvents formula]++"\n"++
>       "  -- The set of events that can occur in any state of the automata\n"++
>       "  RunEvents = "++
>       -- We allow any event to occur that is not the blocked event, which must
>       -- be explicitly unblocked in a state where it it used.
>       makeUnion 4 [makeEventSet an e [] 8 | e <- allEvents formula, e /= ev]++"\n"++
>       "exports\n\n"++
>       "  -- The automata\n"++
>       "  SPEC =\n"++
>       "    let\n"++
>       outputAutomatonStates an aut'++
>       "    within\n"++
>       if agentId `elem` [v | (v,_,_,_) <- actvts an] then
>           "      STATE_0()\n\n"
>       else
>           "      "++interleave ["STATE_0("++agentName++")" | agentName <- agentsToCheck]++"\n\n"

>outputAutomatonStates :: Annotated -> Automaton -> Output
>outputAutomatonStates an aut =
>   let
>       (_,states,_) = aut
>   in
>       flatmap (outputState an aut) states

>outputState :: Annotated -> Automaton -> State -> Output
>outputState an aut st =
>   let
>       (es,boundVars,blockState,id) = st
>       transistions = getTransitionsFromState aut id
>       showTransition (_,toId,e) =
>           "("++makeEventString an e boundVars++" -> STATE_"++show toId++"("++
>           commaConcat bVs++"))\n"
>           where (_,bVs,_,_) = getStateById aut toId
>       self = "STATE_"++show id++"("++commaConcat boundVars++")"
>       runProc = "([] e : RunEvents @ e -> "++self++")\n"
>       allowProc = 
>           case blockState of
>               Allow e -> "("++makeEventString an e boundVars++" -> "++self++")\n"
>   in 
>       "      "++self++" =\n"++
>       makeExternalChoice (runProc:
>           (if blockState /= Blocked then [allowProc] else [])++
>           map showTransition transistions)

>makeExternalChoice :: [String] -> String
>makeExternalChoice ps =
>    if length ps == 1 then spaces 8++concat ps
>    else spaces 8++foldr1 (\p1 -> \p2 -> p1++spaces 8++"[] "++p2) ps

Make external choice over all possible messages that are allowed at this point.

>makeEventString :: Annotated -> TLEvent -> [VarName] -> String
>makeEventString an e boundVars = 
>   let
>       (_,_,parity, no, varsToBind) = e
>       -- Message from the protocol description
>       (_, _, sender, recipient, m, _, senderExtras, receiverExtras) = 
>           head (filter (\(_,n,_,_,_,_,_,_) -> n == no) (protdesc an))
>       msgAtoms = if parity == Send then atomsSend m else atomsRec m
>       msgVarFields = if parity == Send then senderFields m else receiverFields m
>       extractAgent (Agent a) = [a]
>       extractAgent _ = []
>       varsToChoose = 
>           remdups ((extractAgent sender++extractAgent recipient++msgAtoms++
>              (if parity == Send then senderExtras else receiverExtras))
>           \\ boundVars)
>       memberString = if hasFlag an UnboundedParallel then "member("++msg++","++set++") & \n"++spaces 10 else ""
>           where
>               msg = if parity == Send then
>                       if recipient == Environment then
>                           "(Env"++no++","++showSenderMsg an m++",<"++commaConcat senderExtras++">)" 
>                       else
>                           "(Msg"++no++","++showSenderMsg an m++",<"++commaConcat senderExtras++">)" 
>                     else if sender == Environment then
>                           "(Env"++no++","++showReceiverMsg an m++",<"++commaConcat receiverExtras++">)"
>                     else 
>                       "(Msg"++no++","++showReceiverMsg an m++",<"++commaConcat receiverExtras++">)"
>               set = if parity == Send then "SYSTEM_M::OUTPUT_INT_MSG"++no 
>                     else "SYSTEM_M::INPUT_INT_MSG"++no
>       choicesStr = concat ["[] "++v++" : "++setForVar an varsToBind msgVarFields v++" @ " 
>                               | v <- varsToChoose]
>   in
>       choicesStr++(maybeString (choicesStr /= "") "\n"++spaces 10++memberString)++
>       makeEventMessage an False False e

Make the actual message string.

>makeEventMessage :: Annotated -> Bool -> Bool -> TLEvent -> String
>makeEventMessage an useInternalChannels intruderAsSender 
>       (agent, otherAgent, parity, no, vars) = 
>   let
>       -- Message from the protocol description
>       (_, _, sender, recipient, m, _, senderExtras, receiverExtras) = 
>           head (filter (\(_,n,_,_,_,_,_,_) -> n == no) (protdesc an))
>       extract (Agent a) = a
>       channel = 
>           if parity == Send then if useInternalChannels then "internalAgentSend" else "send"
>           else "receive"
>   in
>       case parity of
>           Send    -> case recipient of
>                       Agent a ->
>                           channel++"."++
>                           (if intruderAsSender then intruderId an else extract sender)
>                           ++"."++a++".(Msg"++no++","++
>                           showSenderMsg an m++",<"++commaConcat senderExtras++">)"
>                       Environment ->
>                           "env."++extract sender++".(Env"++no++","++showSenderMsg an m++
>                           ",<"++commaConcat senderExtras++">)"
>           Receive -> case sender of
>                       Agent a ->
>                           channel++"."++a++"."++extract recipient++".(Msg"++no++","++
>                           showReceiverMsg an m++",<"++commaConcat receiverExtras++">)"
>                       Environment ->
>                           "env."++extract recipient++".(Env"++no++","++showSenderMsg an m++
>                           ",<"++commaConcat senderExtras++">)"

Make set of events.

>makeEventSet :: Annotated -> TLEvent -> [VarName] -> Int -> String
>makeEventSet an e boundVars indent = 
>  let
>  (_, _, parity, no, varsToBind) = e
>  -- Message from the protocol description
>  (_, _, sender, recipient, m, _, senderExtras, receiverExtras) = 
>     head (filter (\(_,n,_,_,_,_,_,_) -> n == no) (protdesc an))
>  msgAtoms = if parity == Send then atomsSend m else atomsRec m
>  maybeExtract (Agent a) = [a]
>  maybeExtract _ = []
>  msgVarFields = if parity == Send then senderFields m else receiverFields m
>  varsToChoose = sortremdups ((
>    maybeExtract sender ++ maybeExtract recipient ++msgAtoms++
>    (if parity == Send then senderExtras else receiverExtras))
>      \\ boundVars)
>  memberString = "\n"++spaces indent++"   member("++msg++","++set++")"
>  msg = 
>    if parity == Send then
>      if recipient == Environment then
>        "(Env"++no++","++showSenderMsg an m++",<"++commaConcat senderExtras++">)" 
>      else
>        "(Msg"++no++","++showSenderMsg an m++",<"++commaConcat senderExtras++">)" 
>    else if sender == Environment then
>      "(Env"++no++","++showReceiverMsg an m++",<"++commaConcat receiverExtras++">)"
>    else 
>     "(Msg"++no++","++showReceiverMsg an m++",<"++commaConcat receiverExtras++">)"
>  set = if parity == Send then "SYSTEM_M::OUTPUT_INT_MSG"++no 
>              else "SYSTEM_M::INPUT_INT_MSG"++no
>  in
>    "{ "++makeEventMessage an False False e++
>     maybeString (varsToChoose /= []) (
>       "\n"++spaces indent++" | "++
>       commaConcat (
>         [v++" <- "++setForVar an varsToBind msgVarFields v | v <- varsToChoose]++
>         if hasFlag an UnboundedParallel then [memberString] else []
>       ))
>     ++"}"

Returns a set containing values that the free variable given can take. Also, 
if the variable is substituted for (in boundVars) then a singleton set is 
returned instead.

>setForVar :: Annotated -> [BoundVar] -> [VarField] -> VarName -> String
>setForVar an boundVars messageFields v =
>   let
>       t = findtypeT an v
>       playerTypes = remdups [findtype an v | (v,_,_,_,_) <- procs an]
>       substitutedArgs = [fv | Substitution fv _ <- boundVars]
>       forwardedVars = [(v,m) | Subst v m <- messageFields]
>   in
>       if v `elem` substitutedArgs then 
>           "{"++head [actVar | Substitution fv actVar <- boundVars, fv==v]++"}"
>       else if v `elem` map fst forwardedVars then
>           head [typeSet an vn m | (vn,m) <- forwardedVars, vn == v]
>       else t

*******************************************************************************
System Process Output
*******************************************************************************

>commaNLIfNotEmpty s = if s == "" then s else ",\n"++spaces 10++s++"\n"

Set of pairs (ded, f) indicating that infer.ded should be renamed to 
f where ded is an inference of the form (Sent.(M,T), fs_).

>makeInternalAgentRenaming :: 
>  Annotated -> (String,String,Parity,String,[BoundVar]) -> String
>makeInternalAgentRenaming an 
>    (e @ (agent, otherAgent, parity, msgNo, varsToBind)) =
>  "{(f_, "++makeEventMessage an True False e++")\n"++
>  spaces 6++"  | "++showMsg an fs++" @@ f_ <- INTRUDER_M::KnowableFact"++
>  -- commaNLIfNotEmpty (commaConcat ()) ++
>  commaNLIfNotEmpty (commaConcat (
>    makeRIGens rens ++
>    filter ((/=) "")
>      [let set = setForVar an varsToBind msgVarFields v
>       in maybeString(set /= findtypeT an v) ("member("++v++","++set++")")
>         | v <- msgAtoms]))++
>  spaces 6++"}"
>  where
>    msgAtoms = 
>     sortremdups (vars++if parity == Send then atomsSend m else atomsRec m)
>    msgVarFields = if parity==Send then senderFields m else receiverFields m
>    sentmsg = hd [sentmsg | (_,sentmsg,_,_,_,n) <- sentrep an, n == msgNo]
>    Sent _ tag =  sentmsg
>    vars = [v | Atom v <- tag]
>    (_, _, sender, recipient, m, _, senderExtras, receiverExtras) = 
>       head (filter (\(_,n,_,_,_,_,_,_) -> n == msgNo) (protdesc an))
>    (fs, rens) = newNames (senderMsg sentmsg)

>outputSystem :: Annotated -> TemporalLogicSpec -> Output
>outputSystem an f =
>  let
>  sendEvents = filter (\(_,_,p,_,_) -> p == Send) (allEvents f)
>  -- Set of pairs (ded, f) indicating that infer.ded should be renamed to f
>  makeIntruderSendsRenaming e =
>     -- The intruder cannot take the role of the sender if the following is
>     -- true and therefore don't do the renaming
>     if parity == Send && senderVar `elem` [av | (av,_,_,_) <- actvts an] 
>        && not (senderVar == intruderId an) then ""
>     else
>       "{(f_, "++makeEventMessage an True True e++")\n"++
>       spaces 6++"  | "++f++" @@ f_ <- INTRUDER_M::KnowableFact"++
>       commaNLIfNotEmpty (commaConcat (
>         [v++" <- "++setForVar an varsToBind msgVarFields v | 
>            v <- varsToGenerate]++
>         filter ((/=) "")
>           [let set = setForVar an varsToBind msgVarFields v
>            in maybeString (set/=findtypeT an v) ("member("++v++","++set++")")
>               | v <- msgAtoms]))++
>       spaces 6++"}"
>       where
>         msgAtoms = atomsSend m
>         msgVarFields = senderFields m
>         varsToGenerate = 
>           -- We don't generate the sender as it is the intruder
>           sortremdups (senderExtras++maybeExtract recipient) \\ msgAtoms
>         f = showSenderMsg an m
>         (senderVar, _, parity, msgNo, varsToBind) = e
>         (_, _, sender, recipient, m, _, senderExtras, _) = 
>           head (filter (\(_,n,_,_,_,_,_,_) -> n == msgNo) (protdesc an))
>  maybeExtract (Agent a) = [a]
>  maybeExtract _ = []
>   in
>       "  -- Set of pairs (ded,rn) such that infer.ded is renamed to rn\n"++
>       "  Renaming ="++
>       makeUnion 4 (
>         filter (/= "") (map makeIntruderSendsRenaming sendEvents ++
>         if hasFlag an UnboundedParallel 
>         then map (makeInternalAgentRenaming an) sendEvents
>         else []))
>       ++"\n"++
>       "  -- The system for testing this specification\n"++
>       "  (SYSTEM_SPEC, Deductions) = \n"++
>       "    TEMPORAL_SPEC_COMMON_M::SYSTEM(Renaming, AlphaSpec)\n\n"

