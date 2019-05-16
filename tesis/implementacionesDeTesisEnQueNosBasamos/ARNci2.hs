module ARNci2 (Color(R,B), RB(E,Node), member,insert,delete) where

data Color = R | B deriving (Eq)
data RB a = E | Node Color (RB a) a (RB a) | Blacken (RB a)

color :: RB a -> Color
color E = B
color (Node c _ _ _) = c

make :: Color -> RB a -> RB a
make c E = E
make c (Node _ l a r) = Node c l a r

blacken :: RB a -> RB a
blacken t | color t == R = make B t
          | otherwise = Blacken t

paint :: Color -> RB a -> RB a
paint R t = t
paint B t = blacken t

unBlack :: RB a -> RB a
unBlack (Blacken t) = t
unBlack t = t

member :: Ord a => a -> RB a -> Bool
member a E = False
member a (Node _ l b r) = case compare a b of
                          LT -> member a l
                          EQ -> True
                          GT -> member a r

insert :: Ord a => a -> RB a -> RB a
insert a t = make B (ins t)
             where
             ins E = Node R E a E
             ins (Node c l b r) = case compare a b of
                              LT -> bal c (ins l) b r
                              EQ -> Node c l a r
                              GT -> bal c l b (ins r)

bal:: Color -> RB a -> a -> RB a -> RB a
bal B (Node R (Node R a x b) y c) z d = Node R (Node B a x b) y (Node B c z d)
bal B (Node R a x (Node R b y c)) z d = Node R (Node B a x b) y (Node B c z d)
bal B a x (Node R b y (Node R c z d)) = Node R (Node B a x b) y (Node B c z d)
bal B a x (Node R (Node R b y c) z d) = Node R (Node B a x b) y (Node B c z d)
bal c a x b = Node c a x b



delete :: Ord a => a -> RB a -> RB a
delete a t = unBlack (del t)
             where
             del E = E
             del (Node c l b r)
                | a < b = lbal c (del l) b r
                | a > b = rbal c l b (del r)
                | otherwise = join c l r

lbal :: Color -> RB a -> a -> RB a -> RB a
lbal c (Blacken t1) a1 (Node R t2 a2 t3) = Node c (lbal R (Blacken t1) a1 t2) a2 t3
lbal c (Blacken t1) a1 (Node B (Node R t2 a2 t3) a3 t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
lbal c (Blacken t1) a1 (Node B t2 a2 (Node R t3 a3 t4)) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
lbal c (Blacken t1) a1 (Node B t2 a2 t3) = blacken (Node c t1 a1 (Node R t2 a2 t3))
lbal c t1 a1 t2 = Node c t1 a1 t2

rbal :: Color -> RB a -> a -> RB a -> RB a
rbal c (Node R t1 a1 t2) a2 (Blacken t3) = Node c t1 a1 (rbal R t2 a2 (Blacken t3))
rbal c (Node B t1 a1 (Node R t2 a2 t3)) a3 (Blacken t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
rbal c (Node B (Node R t1 a1 t2) a2 t3) a3 (Blacken t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
rbal c (Node B t1 a1 t2) a2 (Blacken t3) = blacken (Node c (Node R t1 a1 t2) a2 t3)
rbal c t1 a1 t2 = Node c t1 a1 t2

join :: Color -> RB a -> RB a -> RB a
join c l r = case splitLeftmost r of
             Nothing -> paint c l
             Just (a, r') -> rbal c l a r'

splitLeftmost :: RB a -> Maybe (a, (RB a))
splitLeftmost E = Nothing
splitLeftmost (Node c l a r) = case splitLeftmost l of
                               Nothing -> Just (a, (paint c r))
                               Just (a', l') -> Just (a', (lbal c l' a r))
