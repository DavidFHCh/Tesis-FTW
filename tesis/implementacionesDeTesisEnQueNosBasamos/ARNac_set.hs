import ARNac

class Set s where
	empty :: Ord a => s a 
	single :: Ord a => a -> s a
        size :: s a -> Int
        member :: Ord a => a -> s a -> Bool	
	insert1 :: Ord a => a -> s a -> s a
	delete :: Ord a => a -> s a -> s a
        fromList :: Ord a => [a] -> s a
	toList :: s a -> [a]

instance Set RB where
	empty = E

	single x = T B E x E

        size E = 0
	size (T _ E x E) = 1
	size (T _ tl x tr) = 1 + size tl + size tr

        member = ARNac.member
        
	insert1 = ARNac.insert

	delete = ARNac.deleteRB

   	fromList = foldr insert E

	toList E = []
	toList (T c tl x tr) = toList tl ++ [x] ++ toList tr 
