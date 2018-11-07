data ABB a = E | T (ABB a) a (ABB a) deriving Show

checkABB :: Ord a => ABB a -> Bool
checkABB E = True
checkABB (T l x r) = checkABB l && checkABB r && minT x r && maxT x l

minT :: Ord a => a -> ABB a -> Bool
minT x E = True
minT x (T l y r) = minT x l && minT x r && x < y

maxT :: Ord a => a -> ABB a -> Bool
maxT x E = True
maxT x (T l y r) = maxT x l && maxT x r && x > y

member :: Ord a => a -> ABB a -> Bool
member x E = False
member x (T tl y tr)
					| x<y = member x tl
					| x>y = member x tr
					| otherwise = True

insert :: Ord a => a -> ABB a -> ABB a
insert x E = T E x E
insert x (T tl y tr)
					| x < y = T (insert x tl) y tr
					| x > y = T tr y (insert x tr)
					| otherwise = T tl y tr

remove :: Ord a => a -> ABB a -> ABB a
remove x E = E
remove x (T l y E) | x==y = l
remove x (T E y r) | x==y = r
remove x (T l y r)
                   | x<y  = T (remove x l) y r
                   | x>y  = T l y (remove x r)
                   | x==y = let k = minTree r in T l k (remove k r)

minTree :: Ord a => ABB a -> a
minTree (T E y r) = y
minTree (T l x r) = minTree l
