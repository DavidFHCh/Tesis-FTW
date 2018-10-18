import ARNci2

class Set s where
	empty :: Ord a => s a 
	single :: Ord a => a -> s a
        size :: s a -> Int
        member :: Ord a => a -> s a -> Bool	
	insert2 :: Ord a => a -> s a -> s a
	delete :: Ord a => a -> s a -> s a
        fromList :: Ord a => [a] -> s a
	toList :: s a -> [a]

instance Set RB where
	empty = E

	single x = Node B E x E

        size E = 0
	size (Node _ E x E) = 1
	size (Node _ tl x tr) = 1 + size tl + size tr

        member = ARNci2.member
        
	insert2 = ARNci2.insert

	delete = ARNci2.delete

   	fromList = foldr insert E

	toList E = []
	toList (Node c tl x tr) = toList tl ++ [x] ++ toList tr 
