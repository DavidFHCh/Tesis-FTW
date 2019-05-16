
module ARNta (EmptyT(E), PRed(C,R), AddBLayer(B), RBT(Zero, Suc), member,insert,delete) where

data EmptyT a = E deriving Show
type Tr t a = (t a,a,t a)
data PRed t a = C (t a) | R (Tr t a)

instance (Show (t a), Show a) => Show (PRed t a)
 where showsPrec _ (C t) = shows t
       showsPrec _ (R(a,b,c)) =
	    ("R ("++) . shows a . (","++) . shows b . (","++) . shows c . (")"++)

data AddBLayer t a = B(Tr(PRed t) a) deriving Show

data RBT t a = Zero (t a) | Suc (RBT (AddBLayer t) a)

instance (Show (t a),Show a) => Show (RBT t a)
    where
    show (Zero t) = show t
    show (Suc t) = show t

type RBTree a = RBT EmptyT a

member :: Ord a => a -> RBTree a -> Bool
member x t = rbmember x t (\ E -> False)

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

type RR t a = PRed (PRed t) a
type RL t a = PRed (AddBLayer t) a

balance :: RR t a -> a -> RR t a -> RL t a
balance (R a) y (R b) = R(B a,y,B b)
balance (C a) x b = balanceR a x b
balance a x (C b) = balanceL a x b

balanceR :: PRed t a -> a -> RR t a -> RL t a
balanceR a x (R(R(b,y,c),z,d)) = R(B(a,x,C b),y,B(C c,z,d))
balanceR a x (R(b,y,R(c,z,d))) = R(B(a,x,b),y,B(C c,z,C d))
balanceR a x (R(C b,y,C c)) = C(B(a,x,R(b,y,c)))
balanceR a x (C b) = C(B(a,x,b))

balanceL :: RR t a -> a -> PRed t a -> RL t a
balanceL (R(R(a,x,b),y,c)) z d = R(B(C a,x,C b),y,B(c,z,d))
balanceL (R(a,x,R(b,y,c))) z d = R(B(a,x,C b),y,B(C c,z,d))
balanceL (R(C a,x,C b)) z d = C(B(R(a,x,b),z,d))
balanceL (C a) x b = C(B(a,x,b))

class Insertion t where ins :: Ord a => a -> t a -> PRed t a
instance Insertion EmptyT where ins x E = R(E,x,E)

instance Insertion t => Insertion (AddBLayer t) where
	ins x t@(B(l,y,r))
	    | x<y = balance(ins x l) y (C r)
	    | x>y = balance(C l) y (ins x r)
	    | otherwise = C t

instance Insertion t => Insertion (PRed t) where
	ins x (C t) = C(ins x t)
	ins x t@(R(a,y,b))
	    | x<y = R(ins x a,y,C b)
	    | x>y = R(C a,y,ins x b)
	    | otherwise = C t

insert :: Ord a => a -> RBTree a -> RBTree a
insert = rbinsert

rbinsert :: (Ord a,Insertion t) => a -> RBT t a -> RBT t a
rbinsert x (Zero t) = blackenIns(ins x t)
rbinsert x (Suc t) = Suc (rbinsert x t)

blackenIns :: PRed t a -> RBT t a
blackenIns (C u) = Zero u
blackenIns (R(a,x,b)) = Suc(Zero(B(C a,x,C b)))

class Append t where app :: t a -> t a -> PRed t a

instance Append EmptyT where app E E = C E

instance Append t => Append (PRed t) where
    app (C x) (C y) = C(app x y)
    app (C t) (R(a,x,b)) = R(app t a,x,C b)
    app (R(a,x,b)) (C t) = R(C a,x,app b t)
    app (R(a,x,b))(R(c,y,d)) = threeformR a x (app b c) y d

threeformR:: t a -> a -> PRed t a -> a -> t a -> RR t a
threeformR a x (R(b,y,c)) z d = R(R(a,x,b),y,R(c,z,d))
threeformR a x (C b) y c = R(R(a,x,b),y,C c)

instance Append t => Append (AddBLayer t) where
    app (B(a,x,b)) (B(c,y,d)) = threeformB a x (app b c) y d

threeformB :: PRed t a -> a -> RR t a -> a -> PRed t a -> RL t a
threeformB a x (R(b,y,c)) z d = R(B(a,x,b),y,B(c,z,d))
threeformB a x (C b) y c = balleftB (C a) x (B(b,y,c))

balleftB :: RR t a -> a -> AddBLayer t a -> RL t a
balleftB bl x (B y) = balance bl x (R y)

balleft :: RR t a -> a -> RL t a -> RR (AddBLayer t) a
balleft (R a) y c = R(C(B a),y,c)
balleft (C t) x (R(B(a,y,b),z,c)) = R(C(B(t,x,a)),y,balleftB (C b) z c)
balleft b x (C t) = C (balleftB b x t)

balrightB :: AddBLayer t a -> a -> RR t a -> RL t a
balrightB (B y) x t = balance (R y) x t

balright :: RL t a -> a -> RR t a -> RR (AddBLayer t) a
balright a x (R b) = R(a,x,C(B b))
balright (R(a,x,B(b,y,c))) z (C d) = R(balrightB a x (C b),y,C(B(c,z,d)))
balright (C t) x b = C (balrightB t x b)

class Append t => Delred t where
	delTup :: Ord a => a -> Tr t a -> PRed t a
	delLeft :: Ord a => a -> t a -> a -> PRed t a -> RR t a
	delRight :: Ord a => a -> PRed t a -> a -> t a -> RR t a

class Append t => Del t where
	del :: Ord a => a -> AddBLayer t a -> RR t a

class (Delred t, Del t) => Deletion t

instance Delred EmptyT where
	delTup z t@(E,x,E) = if x==z then C E else R t
	delLeft x E y b = R(C E,y,b)
	delRight x a y E = R(a,y,C E)

instance Deletion t => Delred (AddBLayer t) where
	delTup z (a,x,b)
		| z<x = balleftB (del z a) x b
		| z>x = balrightB a x (del z b)
		| otherwise = app a b
	delLeft x a y b = balleft (del x a) y b
	delRight x a y b = balright a y (del x b)

instance Delred t => Del t where
	del z (B(a,x,b))
	    | z<x = delfromLeft a
	    | z>x = delfromRight b
            | otherwise = app a b
              where delfromLeft(C t) = delLeft z t x b
                    delfromLeft(R t) = R(delTup z t,x,b)
                    delfromRight(C t) = delRight z a x t
		    delfromRight(R t) = R(a,x,delTup z t)

instance Deletion EmptyT
instance Deletion t => Deletion (AddBLayer t)

rbdelete :: (Ord a,Deletion t) => a -> RBT (AddBLayer t) a -> RBT t a
rbdelete x (Zero t) = blackenDel (del x t)
rbdelete x (Suc t) = Suc (rbdelete x t)

blackenDel :: RR t a -> RBT t a
blackenDel (C(C t)) = Zero t
blackenDel (C(R(a,x,b))) = Suc(Zero(B(C a,x,C b)))
blackenDel (R p) = Suc(Zero(B p))

delete:: Ord a => a -> RBTree a -> RBTree a
delete x (Zero E) = Zero E
delete x (Suc u) = rbdelete x u
