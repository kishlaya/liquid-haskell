import Data.Set

---------------------------------------------------------------------------------------
{-@ type TRUE = { v:Bool | v } @-}
{-@ type FALSE = { v:Bool | not v } @-}

{-@ type Implies P Q = {v:_ | v <=> (P => Q)} @-}

{-@ implies :: p:Bool -> q:Bool -> Implies p q @-}
implies False _ = True
implies _ True = True
implies _ _ = False

{-@ prop_one_plus_one_eq_two :: _ -> TRUE @-}
prop_one_plus_one_eq_two x = (x == 1 + 1) `implies` (x == 2)

{-@ prop_x_y_200 :: _ -> _ -> TRUE @-}
prop_x_y_200 x y = ((x < 100) && (y < 100)) `implies` (x+y < 200)

---------------------------------------------------------------------------------------
{-@ empty :: {v:Set a | v = empty} @-}

{-@ member :: (Ord a) =>  x:a -> s:Set a -> {v:Bool | v <=> member x s} @-}

{-@ singleton :: x:a -> {v:Set a | v = singleton x} @-}

{-@ union :: (Ord a) => x:Set a -> y:Set a -> {v:Set a | v = union x y} @-}

{-@ intersection :: (Ord a) => x:Set a -> y:Set a -> {v:Set a | v = intersection x y} @-}

{-@ difference :: (Ord a) => x:Set a -> y:Set a -> {v:Set a | v = difference x y} @-}

---------------------------------------------------------------------------------------
{-@ prop_intersection_comm :: _ -> _ -> TRUE @-}
prop_intersection_comm x y = (x `intersection` y) == (y `intersection` x)

{-@ prop_intersection_assoc :: _ -> _ -> TRUE @-}
prop_union_assoc x y z = (x `union` (y `union` z)) == (x `union` y) `union` z

{-@ prop_intersection_dist :: _ -> _ -> _ -> True @-}
prop_intersection_dist x y z = x `intersection` (y `union` z) == (x `intersection` y) `union` (x `intersection` z)
