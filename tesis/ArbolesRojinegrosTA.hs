module ARNTA
where

    data Perfect a = Zero a | Succ (Perfect (a,a)) --ejemplo--


    data EmptyT a = E deriving Show

    type Tr t a = (t a,a,t a)
    data PRed t a = C (t a) | R (Tr t a)

    data AddBLayer t a = B(Tr(PRed t) a) deriving Show

    data RBT t a = Zero (t a) | Suc (RBT (AddBLayer t) a)

    type Tr EmptyT a = (EmptyT a,a,EmptyT a)

    data PRed EmptyT a = C (EmptyT a) | R (Tr EmptyT a)

    data AddBLayer t a = B(Tr(PRed t) a) deriving Show

    data RBT t a = Zero (t a) | Suc (RBT (AddBLayer t) a)

    data AddBLayer EmptyT a = B(Tr(PRed EmptyT) a)

    data RBT EmptyT a = Zero (EmptyT a) | Suc (RBT (AddBLayer EmptyT) a)

    data RBT (AddBLayer EmptyT) a = Zero ((AddBLayer EmptyT) a)
    | Suc (RBT (AddBLayer (AddBLayer EmptyT)) a)

    type RBTree a = RBT EmptyT a


    member :: Ord a => a -> RBTree a -> Bool
    member x t = rbmember x t (\ _ -> False)

    rbmember :: Ord a => a -> RBT t a -> (t a->Bool) -> Bool
    rbmember x (Zero t) m = m t
    rbmember x (Suc u) m = rbmember x u (ablmem x m)

    ablmem :: Ord a => a -> (t a->Bool) -> AddBLayer t a -> Bool
    ablmem x m (B(l,y,r))
    | x<y = prmem x m l
    | x>y = prmem x m r
    | otherwise = True

    prmem :: Ord a => a -> (t a->Bool) -> PRed t a->Bool
    prmem x m (C t) = m t
    prmem x m (R(l,y,r))
    | x<y = m l
    | x>y = m r
    | otherwise = True
