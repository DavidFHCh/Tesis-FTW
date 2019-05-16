{-
Matthew Might implementación
Extensión implementación Okasaki
-}
module ARNac (Color(R,B), RB(E,T), member,insert,deleteRB) where

data Color = R | B | BB | NB deriving Show
data RB a = E | EBB | T Color (RB Int) Int (RB Int) deriving Show

insert :: Int -> RB Int -> RB Int
insert x s = T B a z b where
             T _ a z b = ins s
	     ins E = T R E x E
	     ins s@(T B a y b)
					| x<y = balance B (ins a) y b
					| x>y = balance B a y (ins b)
					| otherwise = s
             ins s@(T R a y b)
					| x<y = T R (ins a) y b
					| x>y = T R a y (ins b)
					| otherwise = s

member Int -> RB a -> Bool
member x E = False
member x (T _ a y b)
					| x<y = member x a
					| x>y = member x b
					| otherwise = True

-- Borrado

redden:: RB a -> RB a
redden (T c a x b) = T R a x b
redden E = error "invariance violation"
redden EBB = error "nunca se cae en este caso"

blacken:: RB a -> RB a
blacken (T c a x b) = T B a x b
blacken EBB = E
blacken E = E

sucBlack:: Color -> Color
sucBlack NB = R
sucBlack R = B
sucBlack B = BB
sucBlack BB = error "no hay suc para BB"

predBlack:: Color -> Color
predBlack R = NB
predBlack B = R
predBlack BB = B
sucBlack NB = error "no hay suc para NB"

sucBlackTree :: RB a -> RB a
sucBlackTree (T c a x b) = (T (sucBlack c) a x b)
sucBlackTree E = EBB
sucBlackTree EBB = error "nunca se cae en este caso"

predBlackTree :: RB a -> RB a
predBlackTree (T c a x b) = (T (predBlack c) a x b)
predBlackTree EBB = E
predBlackTree E = error "nunca se cae en este caso"

bubble:: RB a -> RB a
bubble E = E
bubble EBB = EBB
bubble (T B (T B a x b) y EBB) = balance BB (T R a x b) y E
bubble (T R (T B a x b) y EBB) = balance B (T R a x b) y E
bubble (T B (T R a x b) y EBB) = balance BB (T NB a x b) y E
bubble (T B EBB y (T B a z b)) = balance BB E y  (T R a z b)
bubble (T R EBB y (T B a z b)) = balance B E y  (T R a z b)
bubble (T B EBB y (T R a z b)) = balance BB E y  (T NB a z b)
bubble (T c (T BB a y b) x r) = balance (sucBlack c) (predBlackTree (T BB a y b)) x (predBlackTree r)
bubble (T c l x (T BB a y b)) = balance (sucBlack c) (predBlackTree l) x (predBlackTree (T BB a y b))
bubble (T c a x b) = (T c (bubble a) x (bubble b))

balance :: Color -> RB a -> a -> RB a -> RB a
balance B (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance BB (T R a x b) y (T R c z d) = T B (T B a x b) y (T B c z d)
balance BB (T R (T R a x b) y c) z d = T B (T B a x b) y (T B c z d)
balance BB (T R a x (T R b y c)) z d = T B (T B a x b) y (T B c z d)
balance BB a x (T R b y (T R c z d)) = T B (T B a x b) y (T B c z d)
balance BB a x (T R (T R b y c) z d) = T B (T B a x b) y (T B c z d)
balance BB a x (T NB (T B b y c) z (T B d v e)) = T B (T B a x b) y (balance B c z (redden (T B d v e)))
balance BB (T NB (T B d v e) x (T B b y c)) z a = T B (balance B (redden (T B d v e)) x b) y (T B c z a)
balance c a x b = T c a x b

removeMax :: RB a -> RB a
removeMax E = E
removeMax (T c l x E) = removeRoot (T c l x E)
removeMax (T c l x r) = (T c l x (removeMax r))
removeMax EBB = error "nunca se cae en este caso"

removeRoot:: RB a -> RB a
removeRoot (T R E x E) = E
removeRoot (T B E x E) = EBB
removeRoot (T B (T R a x b) y E) = (T B a x b)
removeRoot (T B E y (T R a x b)) = (T B a x b)
removeRoot (T c l x r) = (T c (removeMax l) (getMax l) r)

getMax :: RB a -> a
getMax (T c l x E) = x
getMax (T c l x r) = getMax r
getMax _ = error "nunca se cae en este caso"

delete :: Ord a => a -> RB a -> RB a
delete x E = E
delete x (T c a y b)
					| member x (T c a y b) == True = if x < y then (T c (delete x a) y b)
					                                 else if x > y then (T c a y (delete x b))
					                                 else removeRoot (T c a y b)
					| otherwise = (T c a y b)

deleteRB :: Ord a => a -> RB a -> RB a
deleteRB x t = blacken (bubble (delete x t))
