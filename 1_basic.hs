abs :: Int -> Int
abs x
 | x>0 = x
 | otherwise = -x

{-@ abs' :: Int -> Nat @-}
abs' :: Int -> Int
abs' x
 | x>0 = x
 | otherwise = -x



{-@ factorial :: Nat -> Int @-}
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n-1)




{-@ type Nat = { v:Int | v>=0 } @-}

{-@ type Pos = { v:Int | v>0 } @-}
{-@ type Neg = { v:Int | v<0 } @-}
{-@ type NonZero = { v:Int | v/=0 } @-}

{-@ type Even = { v:Int | v mod 2 == 0 } @-}


