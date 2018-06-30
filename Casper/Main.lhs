Main body

>module Main (main,compile, vcompile, interpret, simplify) where 

>import Maybe1
>import Types
>import Parse
>import TypeCheck
>import Consistency
>import Annotate
>import Compile
>import IO
>import Interpret
>import SecureChannels
>import SimplifyMain
>import UnboundParallel

Set the following flag to True to save files in /tmp, to avoid delays caused
by writing over the network

>--casperlogo = "  ___   ___   ___   ___   ___   __\n || ||  __|| ||__  || || ||_|| ||\n||     ||_||  __|| ||_|| ||__  ||\n||                 ||\n||\n ||_|| "

>saveToTmp :: Bool
>saveToTmp = False
>version :: String
>version = "2.0"
>welcome :: String
>welcome = "Casper version "++version++"\n\n"

>main :: IO()
>main = compile "test"

>vcompile :: String -> IO()
>vcompile = compile0 True

>compile :: String -> IO()
>compile s = catch (compile0 False s) handler

>handler e = 
>  if isIllegalOperation e 
>  then putStr "I/O error (maybe file not found)\nGoodbye\n" 
>  else putStr ("Error: "++show e++"\nGoodbye\n")

>compile0 :: Bool -> String -> IO()
>compile0 b filename = 
>  do putStr (welcome++"Parsing...\n")
>     fromHandle <- openFile (filename ++ ".spl") ReadMode 
>     contents   <- hGetContents fromHandle
>     compile1 b filename contents

>compile1 :: Bool -> String -> String -> IO()
>compile1 b filename conts 
>  | isError parsed    
>      = putStr ("Parse errors:\n" ++ errorMsg parsed++"Goodbye\n")
>  | otherwise
>      = do  putStr "Type checking...\n"  
>            compile2a b filename conts (body parsed)
>  where parsed = parse conts

>compile2a :: Bool -> String -> String -> Input -> IO()
>compile2a b filename conts input =
>   if generatesystem /= DontGenerate then 
>       case generateSystem input of
>           Yes input' -> compile2b b filename conts input'
>           Error s  -> putStr(s++"\nGoodbye\n")
>   else compile2b b filename conts input
>   where
>        (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,generatesystem,_,_,_,_,_,_,
>           _,_,_,_) = input

>compile2b :: Bool -> String -> String -> Input -> IO()
>compile2b b filename conts input =
>--  putStr (show fvts) >> putStr "\n" >> putStr (show vts) >> putStr "\n" >> 
>--  putStr (show fiks) >> putStr "\n" >> putStr (show iks) >> putStr "\n" >>
>  if err /= "" then putStr (err++w++"\nGoodbye\n")
>  else do 
>          putStr w 
>          putStr "Consistency checking...\n" 
>          compile3 b filename conts output
>  where (err,w) = typecheck input
>        (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>	       vts, iks, timestampinfo, inlines, actualAgents, withdraw, 
>	       unboundpar, generatesystem, intruderId,
>          intruderInitKnows, intruderProcs, 
>	       crackables, deductions, guessables, equivs, channels, newchannels, sessinfo) = input
>        newchannels' = fst (collapse newchannels)
>        output = (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, temporalSpecs,
>	  vts, iks, timestampinfo, inlines, actualAgents, withdraw, 
>	  unboundpar, generatesystem, intruderId, intruderInitKnows, intruderProcs, 
>	  crackables, deductions, guessables, equivs, channels, newchannels', sessinfo)

>compile3 :: Bool -> String -> String -> Input -> IO()
>compile3 b filename conts input =
>  if err /= "" then putStr (err++w++"\nGoodbye\n")
>  else do putStr w 
>          putStr "Compiling...\n" 
>          (compile4 b filename) (makeOutput conts version (annotate input))
>  where (err,w) = consistency input

>compile4 :: Bool -> String -> Output -> IO()
>compile4 b filename output = 
>  let outfn = (if saveToTmp then "/tmp/" else "") ++ filename ++ ".csp"
>  in do putStr ("Writing output...\n" ++ (if b then "\n" ++ output else "")) 
>        toHandle <- openFile outfn WriteMode
>        hPutStr toHandle output
>        hClose toHandle
>        putStr ("Output written to " ++ outfn++"\nGoodbye")

==================== Simplifying transformations =======================

>--vsimplify :: String -> IO()
>--vsimplify = simplify0 True version

>simplify :: String -> IO()
>simplify = simplify0  version
