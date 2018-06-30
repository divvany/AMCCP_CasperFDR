>module SimpParse (parse) where

>import Useful
>import Maybe1
>import Pprint
>import Atoms
>import GenParse
>import MiscParse
>import Parse1
>import SimpTypes
>import Msgparse

==========================================================================

The main parsing function

>parse :: String -> Maybe_ SimplInputpd
>parse file = 
>  let sects = (map (\(s,ls) -> (getKeyword s, ls)) . split . 
>               filter (not . comment) . makeLogicalLines . lines)
>                   file
>      badKWerrs =
>        ["Unrecognized keyword: " ++ st ++ "\n" | (None st,_) <- sects]
>      duplicates [] = []
>      duplicates (kw : kws) 
>        | member kw kws      = kw : duplicates kws
>        | otherwise          = duplicates kws
>      duplicateKWerrs = 
>       ["Duplicated keyword: " ++ show kw ++ "\n" | 
>           kw <- duplicates (map fst sects)]
>      warnings = concat (badKWerrs ++ duplicateKWerrs)
>  in 
>  if warnings /= "" then Error warnings 
>  else
>  let mfvinfo = parseFVars (select FreeVars sects)
>      mprocs = parseProcsInfo (select Processes sects)
>      mprotdesc = parseProtDesc (select ProtDesc sects)
>      mspecs = parseSpecs (select Specs sects)
>      msimpls = parseSimpls (select Simps sects)
>      output1 = 
>         (mfvinfo &&& mprocs &&& mprotdesc &&& mspecs &&& msimpls)
>  in 
>  if isError output1 then (let Error e = output1 in Error e) 
>                          -- type coercion hack
>  else
>  let Yes (fvts,fnts,fiks,dtdefs) = mfvinfo
>      Yes procs = mprocs
>      Yes protdesc = mprotdesc
>      Yes ((secrets,auths),_) = mspecs
>      Yes simpls = msimpls
>      fnts' = [(f, Defed dts rt) | (f,(dts,rt)) <- fnts] ++
>              [(f, HashFunction) | (f,t,_) <- fvts, t=="HashFunction"]
>      fvts' = filter ((/= "HashFunction") . (\(_,b,_) -> b)) fvts
>  in Yes (fvts', fnts', fiks, dtdefs, procs, protdesc, secrets, auths, simpls)

==================================================================
Recognize section headers, and convert into keywords

>data Keyword = FreeVars | Processes | ProtDesc | Specs | Simps |
>               Preamble | None String
>               deriving (Eq, Show)

>getKeyword :: Line -> Keyword
>getKeyword "#Preamble" = Preamble
>getKeyword "#Freevariables" = FreeVars
>getKeyword "#Processes" = Processes
>getKeyword "#Protocoldescription" = ProtDesc
>getKeyword "#Specification" = Specs
>getKeyword "#Simplification" = Simps
>getKeyword other = None other

=========================================================================
Parsing the simplifications

>parseSimpls :: [Line] -> Maybe_ Simpls
>parseSimpls ls = combineMaybes [parseSimpl l | l <- ls]

>parseSimpl :: String -> Maybe_ Simpl
>parseSimpl l = topLevel1 parseSimpl1 "Bad Simplification" l

>parseSimpl1 :: Parse Char Simpl
>parseSimpl1 = 
>  word1ws "RemoveFields" ^^> tokenws '[' ^^> termed_comma_list ']'
>     >>> RemoveFields
>  |||
>  word1ws "RemoveHash" ^^> parsemsg >>> RemoveHash
>  |||
>  word1ws "RemoveEncryption" ^^> parsemsg >>> RemoveEncryption 
>  |||
>  word1ws "SwapPairs" ^^> tokenws '(' ^^> ws word ^^^ 
>    tokenws ',' ^^> ws word <^^ tokenws ')'
>	  >>> SwapPairs
>  |||
>  word1ws "Coalesce" ^^> tokenws '[' ^^> termed_comma_list ']'
>     >>> Coalesce
>  |||
>  word1ws "RemoveHashedFields" ^^> parsemsg >>> RemoveHashedFields
>  |||
>  word1ws "RemovePlainAndEnc" >>> (\_ -> RemovePlainAndEnc)

