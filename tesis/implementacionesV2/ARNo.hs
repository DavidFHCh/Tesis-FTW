module ARNo where

data Color = R | B
data RB a = E | T Color (RB a) a (RB a)

member :: Ord a => a -> RB a -> Bool
member x E = False
member x (T _ tl y tr)
  | x<y = member x tl
  | x>y = member x tr
  | otherwise = True

insert :: Ord a => a -> RB a -> RB a
insert x s = T B a z b where
  T _ a z b = ins s
  ins E = T R E x E
  ins s@(T B a y b)
    | x<y = balance (ins a) y b
    | x>y = balance a y (ins b)
    | otherwise = s
  ins s@(T R a y b)
    | x<y = T R (ins a) y b
    | x>y = T R a y (ins b)
    | otherwise = s

balance :: RB a -> a -> RB a -> RB a
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b
