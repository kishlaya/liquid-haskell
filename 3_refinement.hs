
{-@ id :: x:Int -> { v:Int | v==x } @-}
id :: Int -> Int
-- id x = x+1
id x = x


{-@ abs :: x:Int -> { v:Nat | (x>0 => v==x) || v=0-x } @-}
abs :: Int -> Int
abs x
 | x>0 = x
 | otherwise = -x

