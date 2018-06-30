Annotate the data value given by the parser to include additional information
used in code production

>module Annotate(annotate)

>where

>import Atoms
>import Types
>import Annotated 

Modules that do the work:

>import Signals
>import TemporalLogicSpecs
>import UnboundParallel

----------------------------------------------------------------------

Annotate the output of the parser with appropriate extra information

>annotate :: Input -> Annotated
>annotate (fvts_, fnts_, fiks_, dtdefs_, procs_, protdesc_, secrets_, auths_,
>       temporalSpecs_, actvts_, iks_, timestampinfo_, inlines_, actualAgents_,
>	    withdraw_, unboundpar_, generateSystem_, intruderId_, 
>       intruderInitKnows_, intruderProcs_, crackables_, deductions_, 
>       guessables_, equivs_, channels_, newchannels_, sessinfo_) = 
>  let  
>       authsignals_ = createSignals protdesc_ auths_
>       secretsignals_ = createSecretSignals procs_ protdesc_ secrets_
>       extrainfo_ = getAllInfo protdesc_ authsignals_ secretsignals_
>       protdesc' = annotateProtdesc extrainfo_ protdesc_
>       sentrep_ = makeSentRep fvts_ protdesc' 
>       authinfo_ = zip3 [1..] auths_ authsignals_
>       temporalSpecs' = normalizeTemporalSpecs fvts_ actvts_ protdesc' temporalSpecs_ 
>       flags_ = foldr (\(b,f) fs -> if b then f:fs else fs) [] fs
>           where
>               fs = 
>                   [(unboundpar_, UnboundedParallel),
>                       (withdraw_, Withdraw), (timedAuths, TimedAuth),
>                       (timestampsUsed,TimestampsUsed), (timeUsed, TimeUsed),
>                       (guessablesUsed, GuessablesUsed), (crackablesUsed, CrackablesUsed),
>                       (timedCracking, TimedCracking)
>                   ]
>               timestampsUsed =
>                   case timestampinfo_ of
>                       TimeStampsUsed _ _ _ -> True
>                       _ -> False
>               timedCracking = [True  | (_,Just _) <- crackables_] /= []
>               timedAuths = or [isTimedAuth at | (_,_,at) <- auths_]
>               timeUsed = timedCracking || timestampsUsed || timedAuths -- agents perform tocks
>               crackablesUsed = crackables_ /= []
>               guessablesUsed = guessables_ /= []
>  in Annotated {
>       fvts = fvts_,
>       fnts = fnts_,
>       fiks = fiks_,
>       dtdefs = dtdefs_,
>       procs = procs_,
>       protdesc = protdesc',
>       secrets = secrets_,
>       auths = auths_,
>       temporalSpecs = temporalSpecs',
>       actvts = actvts_,
>       iks = iks_,
>       timestampinfo = timestampinfo_,
>       inlines = inlines_,
>       actualAgents = actualAgents_,
>       intruderId = intruderId_,
>       intruderInitKnows = intruderInitKnows_,
>       intruderProcs = intruderProcs_,
>       crackables = crackables_,
>       deductions = deductions_,
>       guessables = guessables_,
>       equivs = equivs_,
>       channels = channels_,
>       newchannels = newchannels_,
>       sessinfo = sessinfo_,
>       authsignals = authsignals_,
>       secretsignals = secretsignals_,
>       extrainfo = extrainfo_,
>       sentrep = sentrep_,
>       authinfo = authinfo_,
>       flags = flags_
>   }

Annotate protocol description with the extras fields

>annotateProtdesc :: [ExtraInfo] -> ProtDesc -> ProtDesc'
>annotateProtdesc extrainfo = map (annotateProtMsg extrainfo)

>annotateProtMsg extrainfo (ass,n,a,b,m,t) =
>  let relinfo = [(c,ls) | (nr,c,ls) <- extrainfo, n==nr]
>      extras d = 
>        let ms = [ls | (c,ls) <- relinfo, d==Agent c]
>        in if ms==[] then [] else head ms
>  in  (ass,n,a,b,m,t, extras a, extras b)
