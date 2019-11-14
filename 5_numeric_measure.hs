
{-@ type NonZero = { v:Int | v/=0 } @-}

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide n d = div n d

{-@ type NList = { v:[Int] | size v > 0 } @-}

{-@ avg :: NList -> Int @-}
avg :: [Int] -> Int
avg xs = divide (sum xs) (size xs)

-- {-@ size :: [a] -> Int @-}
-- size :: [a] -> Int
-- size [] = 0
-- size (x:xs) = 1 + size xs


-----------------------------------------------

{-@ size :: xs:[a] -> { v:Nat | v == size xs } @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs
{-@ measure size @-}
