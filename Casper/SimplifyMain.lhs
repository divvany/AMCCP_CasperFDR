>module SimplifyMain (simplify0) where

>import Maybe1
>import SimpParse
>import TypeCheckpd
>import Consistency
>import Simplify
>import IO
>import SimpTypes
>import SimpTypeCheck

>-- version = "Tester"
>-- welcome = "Simplifying Transformations "++version++"\n"


>simplify0 :: String -> String -> IO()
>simplify0 version filename = 
>  do putStr ("Simplifying Transformations version "++version++"\nParsing...\n")
>     fromHandle <- openFile (filename ++ ".spl") ReadMode 
>     contents   <- hGetContents fromHandle
>     simplify1 contents

>simplify1 :: String -> IO()
>simplify1 conts 
>  | isError parsed    
>      = putStr ("Parse errors:\n" ++ errorMsg parsed)
>  | otherwise
>      = do -- putStr display 
>           putStr "Type checking...\n" 
>           simplify2 (body parsed)
>  where parsed = parse conts
> 	 (fvts, fnts, fiks, _, procs, protdesc, secrets, auths, simpls) =
>          body parsed

        display = show fvts++"\n"++show fnts++"\n"++show fiks++"\n"++
                  show procs++"\n"++concat(map showpd protdesc)++"\n"++
                  show secrets++"\n"++show auths++"\n" ++
                  show simpls++"\n"

>showpd (_,n,a,b,m,_) = show n ++ show a ++ show b ++ show m ++ "\n"

>simplify2 :: SimplInputpd -> IO()
>simplify2 
>	(fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, simpls) =
>  if err /= "" then putStr err
>  else do putStr "Consistency checking...\n" 
>          simplify3
>	    (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, simpls)
>  where err = typecheckpd 
>                (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths)
>	       ++ (simptypecheck fvts fnts simpls)


>simplify3 :: SimplInputpd -> IO()
>simplify3 
>     (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths, simpls) =
>  if err /= "" then putStr (err++w)
>  else do putStr w 
>          putStr "Simplifying...\n" 
>          putStr (simplifications 
>                   (fvts, fnts, fiks, dtdefs, procs, protdesc, 
>                    secrets, auths, simpls)) 
>  where (err,w) = 
>          consistencypd 
>            (fvts, fnts, fiks, dtdefs, procs, protdesc, secrets, auths)


Thought : output of new protocol only on screen not saved to a file.






