Channel collapsing functions

>module SecureChannels (
>   collapse, inUse, channelIs, channelSatisfies, SessionId,
>   channelSelect, sessionids) where

>import Types
>import Annotated
>import Useful

Collapse the channel specifications by collapsing each channel

>collapse :: [NewChannelInfo] -> ([NewChannelInfo], String)
>collapse [] = ([], "")
>collapse ((m, c):chans) = ((m, c'):chans', compare c c' m ++ errs)
>  where c' = channelCollapse c
>        compare x y m = if (channelCompare x y == Equal) then "" else "Warning: channel " ++ m ++ " (" ++ channelShow x ++ ") was collapsed to " ++ channelShow y ++ "\n"
>        (chans', errs) = collapse chans

Collapse a channel by finding the first channel in the valid lattice 
that is less than or equal to it

>channelCollapse :: Channel -> Channel
>channelCollapse c = head (dropWhile (gt c) hierarchy)
>  where gt c1 c2 = let c1_comp_c2 = channelCompare c1 c2 in
>										c1_comp_c2 == Less || c1_comp_c2 == Incomparable

Show a channel

>channelShow :: Channel -> String
>channelShow (0,0,0,0) = "_|_"
>channelShow (c, nf, nh, nr) = cStr ++ nfStr ++ nhStr ++ nrStr
>  where cStr = if c > 0 then "C" ++ (if nf + nh + nr > 0 then " ^ " else "") else ""
>        nfStr = if nf > 0 then "NF" ++ (if nh + nr > 0 then " ^ " else "") else ""
>        nhStr = if nh > 0 then dashNRA ++ (if nr > 0 then " ^ " else "") else ""
>        nrStr = if nr > 0 then dashNR else ""
>        dashNRA = if nh == 1 then "NRA-" else "NRA"
>        dashNR = if nr == 1 then "NR-" else "NR"

Pick out a channel specification

>channelSelect :: MsgNo -> [NewChannelInfo] -> Channel
>channelSelect _ [] = (0,0,0,0)
>channelSelect m ((n,c):ncs) = if m == n then c else channelSelect m ncs

Tests whether a channel is being used

>inUse fs = or . map (channelIs fs . snd)

Test whether a channel satisfies (i.e. >= to) a given specification

>channelSatisfies [] (a,b,c,d) = True
>channelSatisfies (f:fs) cs = h f cs && channelSatisfies fs cs
>  where h "C" (a,b,c,d) = a >= 1
>        h "NF" (a,b,c,d) = b >= 1
>        h "NRA-" (a,b,c,d) = c >= 1
>        h "NRA" (a,b,c,d) = c >= 2
>        h "NR-" (a,b,c,d) = d >= 1
>        h "NR" (a,b,c,d) = d >= 2

Test whether a channel is exactly equal to a given specification

>channelIs [] (a,b,c,d) = a + b + c + d == 0
>channelIs (f:fs) cs = h f cs && channelIs fs (cs' f cs)
>  where h "C" (a,b,c,d) = a == 1
>        h "NF" (a,b,c,d) = b == 1
>        h "NRA-" (a,b,c,d) = c == 1
>        h "NRA" (a,b,c,d) = c == 2
>        h "NR-" (a,b,c,d) = d == 1
>        h "NR" (a,b,c,d) = d == 2
>        cs' "C" (a,b,c,d) = (0,b,c,d)
>        cs' "NF" (a,b,c,d) = (a,0,c,d)
>        cs' "NRA-" (a,b,c,d) = (a,b,0,d)
>        cs' "NRA" (a,b,c,d) = (a,b,0,d)
>        cs' "NR-" (a,b,c,d) = (a,b,c,0)
>        cs' "NR" (a,b,c,d) = (a,b,c,0)

Channel hierarchy shown below:

>hierarchy :: [Channel]
>hierarchy = [(1, 1, 2, 2),
>							(1, 1, 2, 1), (1, 1, 1, 2),
>							(1, 0, 2, 1), (1, 1, 1, 1), (0, 1, 1, 2),
>							(1, 0, 1, 1), (0, 1, 1, 1),
>							(1, 0, 0, 1), (0, 1, 1, 0),
>							(0, 0, 0, 0)]

Compare two points in the full lattice

>channelCompare :: Channel -> Channel -> ChannelComp
>channelCompare (c1, nf1, nh1, nr1) (c2, nf2, nh2, nr2) 
> | c1 == c2 && nf1 == nf2 && nh1 == nh2 && nr1 == nr2 = Equal
> | c1 <= c2 && nf1 <= nf2 && nh1 <= nh2 && nr1 <= nr2 = Less
> | c1 >= c2 && nf1 >= nf2 && nh1 >= nh2 && nr1 >= nr2 = Greater
> | otherwise = Incomparable

                   (1,  1,  2,  2)
                    C   NF  NRA  NR
                  /                \
                 /                  \
          (1,  1,  2,  1)    (1,  1,  1,  2)
           C   NF  NRA  NR-    C   NF  NRA- NR
         /               \  /               \
        /                 \/                 \
(1,  0,  2,  1)    (1,  1,  1,  1)    (0,  1,  1,  2)
 C      NRA  NR-    C   NF  NRA- NR-       NF  NRA- NR
        \                 /\                 /
         \               /  \               /
          (1,  0,  1,  1)    (0,  1,  1,  1)
           C      NRA- NR-       NRA  NRA- NR-
                 |                  |
                 |                  |
          (1,  0,  0,  1)    (0,  1,  1,  0)
           C           NR-      NF  NRA
                 \                  /
                  \                /
                    (0,  0,  0,  0)
                          _|_

>type SessionId = (Int, ([Char], [Char], [Char], [Char], [[Char]]), [Char])

Build a list of all necessary session identifiers

>sessionids :: [SessionInfo] -> ProcessList -> ProtDesc' -> ActualAgents -> [SessionId]

Each session id consists of a process name (e.g. INITIATOR), the name in the protocol
description (e.g. a), the agent's name (e.g. Alice), the message number the session
is initiated with and a unique identifier.

>sessionids sessinfo procs protdesc actualAgents =
>  let actualProcs = [(pid,a,pn) | (pid,pn,_,_,_) <- procs,
>                     (pn',a) <- agentsList, pn'==pn]
>      agentsList = [(pn,head args) | Star (pn,args) <- actualAgents] ++ 
>                   [(pn,head args) | SeqComp pns <- actualAgents, (pn,args) <- pns]
> -- a list of all the messages an agent sends
>      msgs a = [n | (_,n,Agent a',Agent _,_,_,_,_) <- protdesc, a'==a]
> -- a list of all the messages from a session that an agent sends
>      sessmsgs a xs = (msgs a) `intersection` xs
>      sessids = 
> -- normal and injective sessions require one sess id for each participant
>        [(pn, pid, aid, head (sessmsgs pid xs), tail (sessmsgs pid xs)) | 
>         (_,s,xs) <- sessinfo, s < 2, (pid,aid,pn) <- actualProcs, sessmsgs pid xs /= []] ++
> -- symmetric sessions require two session ids
> -- but the responder's is only used if they are communicating with the intruder
>        [(pn, pid, aid, head (sessmsgs pid xs), tail (sessmsgs pid xs)) |
>         (_,2,xs) <- sessinfo, (pid,aid,pn) <- actualProcs, sessmsgs pid xs /= []]
> -- model changed
> -- symmetric sessions require one sess id total ('owned' by initiating agent)
> --       [(pn, pid, aid, head xs, tail xs) | (_,2,xs) <- sessinfo, (pid,aid,pn) <- actualProcs,
> --      (_,n,Agent a,Agent _,_,_,_,_) <- protdesc, a==pid, head xs==n]
>  in
>  map sessIdName (zip [1..length sessids] sessids)
>  where
>    sessIdName (i,(pn, pid, aid, n, ms)) = (i, (pn, pid, aid, n, ms), "c_" ++ [head aid] ++ show i)


    sessIdName (i,(pn, pid, aid, n, ms)) = (i, (pn, pid, aid, n, ms), "c_" ++ pn ++ "_" ++ pid ++ "_" ++ aid ++ "_" ++ n ++ "_" ++ show i)
