import ARNta

class Flatten t where
   flat :: t a -> [a]
   
instance Flatten EmptyT where
   flat E = []
   
instance Flatten t => Flatten (PRed t) where
   flat (C x) = flat x
   flat (R (l,x,r)) = flat l ++ [x] ++ flat r
   
instance Flatten t => Flatten (AddBLayer t) where
   flat (B (l,x,r)) = flat l ++ [x] ++ flat r
   
   
instance Flatten t => Flatten (RBT t) where
  flat (Zero b) = flat b
  flat (Suc b) = flat b
  
class Sizable t where
   size :: t a -> Int
   
instance Sizable EmptyT where
   size E = 0
   
instance Sizable t => Sizable (PRed t) where
   size (C x) = size x
   size (R (l,x,r)) = size l + size r + 1
   
instance Sizable t => Sizable (AddBLayer t) where
   size (B (l,x,r)) = size l + size r + 1
      
instance Sizable t => Sizable (RBT t) where
  size (Zero b) = size b
  size (Suc b) = size b


class Set s where
	empty :: Ord a => s a 
	single :: Ord a => a -> s a
        ssize :: s a -> Int
        member :: Ord a => a -> s a -> Bool	
	insert1 :: Ord a => a -> s a -> s a
	delete :: Ord a => a -> s a -> s a
        fromList :: Ord a => [a] -> s a
	toList :: s a -> [a]

instance Set (RBT EmptyT) where
	empty = Zero E

	single x = Suc(Zero(B(C(E), x, C(E))))

        ssize = size

        member = ARNta.member
        
	insert1 = ARNta.insert

	delete = ARNta.delete

   	fromList = foldr ARNta.insert (Zero E)

	toList = flat


b1 = Suc(Suc(Zero(B(R(B(C(E),1,C(E)),2,B(R(E,3,E),4,R(E,5,E))),
             6,
             C(B(C(E),8,R(E,9,E)))))))

