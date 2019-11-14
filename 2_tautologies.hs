{-@ type TRUE = { v:Bool | v } @-}
{-@ type FALSE = { v:Bool | not v } @-}


{-@ alwaysTrue :: Bool -> TRUE @-}
alwaysTrue p = p || not p


{-@ dne :: Bool -> TRUE @-}
dne p = p <= (not (not p))


{-@ pierce :: Bool -> Bool -> TRUE @-}
pierce :: Bool -> Bool -> Bool
pierce p q = ((p <= q) <= p) <= p
