data Color = R | B deriving (Show, Eq)

data RB a = E | T Color (RB a) a (RB a) deriving Show

minT :: Ord a => a -> RB a -> Bool
minT x E = True
minT x (T _ l y r) = minT x l && minT x r && x < y

maxT :: Ord a => a -> RB a -> Bool
maxT x E = True
maxT x (T _ l y r) = maxT x l && maxT x r && x > y

checkRB :: Ord a => RB a -> Bool
checkRB E = True
checkRB (T R l x r) = False
checkRB t@(T B l x r) = checkIRB l && checkIRB r && minT x r && maxT x l && valAN (an t) t

checkIRB :: RB a -> Bool
checkIRB E = True
checkIRB (T R (T R l y r) x r2) = False
checkIRB (T R l1 x (T R l y r)) = False
checkIRB (T _ l x r) = checkIRB l && checkIRB r

-- numTNB :: RB a -> Int
-- numTNB E = 1
-- numTNB (T R l x r) = numTNB l + numTNB r
-- numTNB (T B l x r) = 1 + numTNB l + numTNB r

-- valAN :: RB a -> Bool
-- valAN E = True
-- valAN (T _ (T B E y E) x E) = False
-- valAN (T _ E x (T B E y E)) = False
-- valAN (T _ (T R E z E) x (T B E y E)) = False
-- valAN (T _ (T B E z E) x (T R E y E)) = False
-- valAN (T _ (T R E z E) x (T R E y E)) = True
-- valAN (T _ (T B E z E) x (T B E y E)) = True
-- valAN (T _ (T R E y E) x E) = True
-- valAN (T _ E x (T R E y E)) = True
-- valAN (T _ l x r) =  valAN l &&  valAN r

an :: RB a -> Int
an E = 0
an (T R l x r) | an l == an r = an l
	       | otherwise = error "violación a la altura negra"
an (T B l x r) | an l == an r = 1 + an l
               | otherwise = error "violación a la altura negra"


valAN :: Int -> RB a -> Bool
valAN n E = an E == 0
valAN n t@(T B l x r) = n == an t && valAN (n-1) l && valAN (n-1) r
valAN n t@(T R l x r) = n == an t && valAN n l && valAN n r



