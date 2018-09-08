--Definicion de arboles binarios
data AB a = E | T (AB a) a (AB a) deriving Show

--Definicion de si un elemento esta en un arbol
member :: Eq a => a -> AB a -> Bool
member x (T l y r) | x == y = True
                   | otherwise = member x l || member x r

--Insercion en arboles binarios
insert :: Eq a => a -> AB a -> AB a
insert x E = T E x E
insert x t@(T l y r) | member x t = t
                     | otherwise = (T l y (insert x r))

--Borrado en arboles binarios
remove :: Eq a => a -> AB a -> AB a
remove x E = E
remove x (T l y E) | x == y = l
remove x (T E y r) | x == y = r
remove x (T l y r) | x == y = join l r
                   | member x l = T (remove x l) y r
                   | member x r = T l y (remove x r)
                   | otherwise = (T l y r)

-- junta dos arboles binarios
join :: Eq a => AB a -> AB a -> AB a
join E r = r
join (T l x r) r2 = let k = mLeft r2
                            in T l x (T r k (remove k r2))
--minimo del arbol izquierdo
mLeft :: AB a -> a
mLeft (T E x r) = r
mLeft (T l x r) = mLeft l

--ARBOLES BINARIOS DE BUSQUEDA--

data ABB a = E | T (ABB a) a (ABB a) deriving Show

--Checa si es arbole binario de busqueda.
checkABB :: Ord a => ABB a -> Bool
checkABB E = True
checkABB (T l x r) = minT x r && maxT x l

minT :: Ord a => a -> ABB a -> Bool
minT x E = True
minT x (T l y r) = maxT x l && minT x r && x < y

maxT :: Ord a => a -> ABB a -> Bool
maxT x E = True
maxT x (T l y r) = maxT x l && maxT x r && x < y

member :: Ord a => a -> ABB a -> Bool
member x E = False
member x (T tl y tr)
                    | x < y = member x tl
                    | x > y = member x tr
                    | otherwise = True

insert :: Ord a => a -> ABB a -> ABB a
insert x E = T E x E
insert x (T tl y tr)
                    | x < y = T (insert x tl) y tr
                    | x > y = T tl y (insert x tr)
                    | otherwise = T tl y tr


remove :: Ord a => a -> ABB a -> ABB a
remove x E = E
remove x (T l y E) | x == y = l
remove x (T E y r) | x == y = r
remove x (T l y r)
                    | x < y = T (remove x tl) y tr
                    | x > y = T tl y (remove x tr)
                    | x == y = let k = minTree r in T l k (remove k r)

minTree:: Ord a => ABB a -> a
minTree (T E x r) = x
minTree (T l x r) = minTree l





-----------------Se acaban los arboles simples---------------------

--ARBOLES ROJINEGROS--

data Color = R | B deriving (Show, Eq)
data RB a = E | T COlor (RB a) a (RB a) deriving Show


alturaNegra :: RB a -> Int
alturaNegra E = 0
alturaNegra (T _ E x E) = 1
alturaNegra (T _ (T c a y b) x tr) = if c == B
                                        then 1+alturaNegra (T c a y b)
                                        else alturaNegra (T c a y b)


member :: Ord a => a -> RB a -> Bool
member x E = False
member x (T _ tl y tr)
                    | x < y = member x tl
                    | x > y = member x tr
                    | otherwise = True

insert :: Ord a => a -> RB a -> RB a
insert x s = T B a z b where T _ a z b = ins s
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
balance (T R (T R a x b) x c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b
