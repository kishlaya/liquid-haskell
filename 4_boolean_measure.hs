
{-@ type NonZero = { v:Int | v/=0 } @-}

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide n d = div n d

{-@ type NList = { v:[Int] | nonEmpty v } @-}

{-@ avg :: NList -> Int @-}
avg :: [Int] -> Int
avg xs = divide (sum xs) (size xs)

-- {-@ size :: [a] -> Int @-}
-- size :: [a] -> Int
-- size [] = 0
-- size (x:xs) = 1 + size xs


-----------------------------------------------

{-@ nonEmpty :: [a] -> Bool @-}
nonEmpty [] = False
nonEmpty _  = True
{-@ measure nonEmpty @-}


{-@ size :: xs:[a] -> { v:Nat | nonEmpty xs => v>0 } @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs
