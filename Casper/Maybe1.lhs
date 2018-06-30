>module Maybe1(
>  Maybe_(Yes, Error), isError, errorMsg, body, 
>  (@@), (&&&), (##), 
>  checkM, combineMaybes  
>  )
>where

>infixl 3 &&&
>infixr 9 @@
>infixr 9 ##

The Maybe_ data type

>data Maybe_ a = Yes a | Error String
>                deriving (Eq, Ord, Show)

======== Select parts

>isError (Yes _) = False
>isError (Error _) = True

>errorMsg (Error err) = err

>body (Yes a) = a

Form cartesian product, or return erros

>(&&&) :: Maybe_ a -> Maybe_ b -> Maybe_ (a,b)
>Yes a &&& Yes b = Yes (a,b)
>Error w &&& Yes _ = Error w
>Yes _ &&& Error w = Error w
>Error w &&& Error w' = Error (w ++ w')

Apply function to Maybe_ argument if possible

>(@@) :: (a -> b) -> Maybe_ a -> Maybe_ b
>_ @@ Error w = Error w
>f @@ Yes a = Yes (f a)

>(##) :: (a -> Maybe_ b) -> Maybe_ a -> Maybe_ b
>_ ## Error w = Error w
>f ## Yes a = f a

Conditional

checkM maybea (p,w) checks that the first argument satisfies p, and gives
error w if not

>checkM :: Maybe_ a -> (a -> Bool, String) -> Maybe_ a
>checkM (Error w) _ = Error w
>checkM (Yes a) (p,w)
>  | p a        = Yes a
>  | otherwise  = Error w


>combineMaybes :: [Maybe_ a] -> Maybe_ [a]
>combineMaybes mas
>  | ws /= []  = Error (concat ws)
>  | otherwise = Yes (map body mas)
>  where ws = [w | Error w <- mas]
