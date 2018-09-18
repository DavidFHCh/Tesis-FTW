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


--Borrado--
delete :: Ord a => a -> RB a -> RB a
delete x t = case del t of {T _ a y b -> T B a y b; _ -> E}
where
del E = E
del (T _ a y b)
    | x<y = delfromLeft a y b
    | x>y = delfromRight a y b
    | otherwise = app a b
delfromLeft a@(T B _ _ _) y b = balleft (del a) y b
delfromLeft a y b = T R (del a) y b

delfromRight a y b@(T B _ _ _) = balright a y (del b)
delfromRight a y b = T R a y (del b)


--convierte una raiz negra a roja--
red :: RB a -> RB a
red (T B a x b) = T R a x b
red _ = error "invariance violation"


--El constructor inteligente ballef t devuelve un árbol balanceado manteniendo de cierta manera el árbol de entrada izquierdo.--
balleft :: RB a -> a -> RB a -> RB a
balleft (T R a x b) y c = T R (T B a x b) y c
balleft bl x (T B a y b) = balance bl x (T R a y b)
balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (red c))



-- barigiht es analogo a balleft--
balright :: RB a -> a -> RB a -> RB a
balright a x (T R b y c) = T R a x (T B b y c)
balright (T B a x b) y bl = balance (T R a x b) y bl
balright (T R a x (T B b y c)) z bl = T R (balance (red a) x b) y (T B c z bl)

--funcion auxuliar que pega dos arboles--
app :: RB a -> RB a -> RB a
app E x = x
app x E = x
app (T R a x b) (T R c y d) =
case app b c of
    T R b’ z c’ -> T R(T R a x b’) z (T R c’ y d)
    bc -> T R a x (T R bc y d)
app (T B a x b) (T B c y d) =
case app b c of
    T R b’ z c’ -> T R(T B a x b’) z (T B c’ y d)
    bc -> balleft a x (T B bc y d)
app a (T R b x c) = T R (app a b) x c
app (T R a x b) c = T R a x (app b c)


-----------Constructores Inteligentes 2---------

data Color = R | B deriving (Show, Eq)
data RB a = E | Node Color (RB a) a (RB a)
              | Blacken (RB a) deriving (Show)


--Obtiene el color del arbol de entrada--
color :: RB a -> Color
color E = B
color (Node c _ _ _) = c


--devuelve un árbol con la raı́z del color que recibe como entrada--
make :: Color -> RB a -> RB a
make c E = E
make c (Node _ l a r) = Node c l a r

--colorear de negro la raı́z del árbol de entrada, puede regresar un arbol binigga--
blacken :: RB a -> RB a
blacken t | color t == R = make B t
          | otherwise = Blacken t

--Agrega una capa negra al arbol del que se elimino un elemento, usando blacken--
paint :: Color -> RB a -> RB a
paint R t = t
paint B t = blacken t

--Se encarga de quitar el constructor Blacken de un arbol.--
unBlack :: RB a -> RB a
unBlack (Blacken t) = t
unBlack t = t


--delete--
delete :: Ord a => a -> RB a -> RB a
delete a t = unBlack (del t)
where
del E = E
del (Node c l b r)
                    | a < b = lbal c (del l) b r
                    | a > b = rbal c l b (del r)
                    | otherwise = join c l r


--construye inteligentemente un árbol roji-negro nuevo sin la capa doble negra. El izquierdo tiene un blacken--
lbal :: Color -> RB a -> a -> RB a -> RB a
lbal c (Blacken t1) a1 (Node R t2 a2 t3) = Node c (lbal R (Blacken t1) a1 t2) a2 t3
lbal c (Blacken t1) a1 (Node B (Node R t2 a2 t3) a3 t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
lbal c (Blacken t1) a1 (Node B t2 a2 (Node R t3 a3 t4)) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
lbal c (Blacken t1) a1 (Node B t2 a2 t3) = blacken (Node c t1 a1 (Node R t2 a2 t3))
lbal c t1 a1 t2 = Node c t1 a1 t2


--construye un árbol roji-negro a partir de un árbol (desarmado), cuyo subárbol derecho era un árbol doble negro.--
rbal :: Color -> RB a -> a -> RB a -> RB a
rbal c (Node R t1 a1 t2) a2 (Blacken t3) = Node c t1 a1 (rbal R t2 a2 (Blacken t3))
rbal c (Node B t1 a1 (Node R t2 a2 t3)) a3 (Blacken t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
rbal c (Node B (Node R t1 a1 t2) a2 t3) a3 (Blacken t4) = Node c (Node B t1 a1 t2) a2 (Node B t3 a3 t4)
rbal c (Node B t1 a1 t2) a2 (Blacken t3) = blacken (Node c (Node R t1 a1 t2) a2 t3)
rbal c t1 a1 t2 = Node c t1 a1 t2


--pega subarboles--
join :: Color -> RB a -> RB a -> RB a
join c l r = case splitLeftmost r of
                Nothing -> paint c l
                Just (a, r’) -> rbal c l a r’

--epara un árbol roji-negro en su elemento más a la izquierda y el árbol que resulta de borrar dicho elemento.--
splitLeftmost :: RB a -> Maybe (a ,(RB a))
splitLeftmost E = Nothing
splitLeftmost (Node c l a r) = case splitLeftmost l of
                Nothing -> Just (a, (paint c r))
                Just (a’, l’) -> Just (a’, (lbal c l’ a r))


--Aritmetica de Colores--

--Colores inciales--
data Color = R | B | BB | NB deriving Show


--EBB es el arbol vacio de color doble negro--
data RB a = E | EBB | T Color (RB a) a (RB a) deriving Show


--redden devuelve un árbol pero cambiando el color de su raı́z a rojo,--
redden:: RB a -> RB a
redden (T c a x b) = T R a x b
redden E = error "invariance violation"

-- lo mismo a redden pero en negro--
blacken:: RB a -> RB a
blacken (T c a x b) = T B a x b
blacken EBB = E
blacken E = E

--artimetica--
sucBlack:: Color -> Color
sucBlack NB = R
sucBlack R = B
sucBlack B = BB

predBlack:: Color -> Color
predBlack R = NB
predBlack B = R
predBlack BB = B

sucBlackTree :: RB a -> RB a
sucBlackTree (T c a x b) = (T (sucBlack c) a x b)
sucBlackTree E = EBB

predBlackTree :: RB a -> RB a
predBlackTree (T c a x b) = (T (predBlack c) a x b)
predBlackTree EBB = E

bubble:: RB a -> RB a
bubble E = E
bubble EBB = EBB
bubble (T B (T B a x b) y EBB) = balance BB (T R a x b) y E
bubble (T R (T B a x b) y EBB) = balance B (T R a x b) y E
bubble (T B (T R a x b) y EBB) = balance BB (T NB a x b) y E
bubble (T B EBB y (T B a z b)) = balance BB E y (T R a z b)
bubble (T R EBB y (T B a z b)) = balance B E y (T R a z b)
bubble (T B EBB y (T R a z b)) = balance BB E y (T NB a z b)
bubble (T c (T BB a y b) x r) =
balance (sucBlack c) (predBlackTree (T BB a y b)) x (predBlackTree r)
bubble (T c l x (T BB a y b)) =
balance (sucBlack c) (predBlackTree l) x (predBlackTree (T BB a y b))
bubble (T c a x b) = (T c (bubble a) x (bubble b))

--version extendida de balance de Okasaki--

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

removeRoot:: RB a -> RB a
removeRoot (T R E x E) = E
removeRoot (T B E x E) = EBB
removeRoot (T B (T R a x b) y E) = (T B a x b)
removeRoot (T B E y (T R a x b)) = (T B a x b)
removeRoot (T c l x r) = (T c (removeMax l) (getMax l) r)

getMax :: RB a -> a
getMax (T c l x E) = x
getMax (T c l x r) = getMax r


delete :: Ord a => a -> RB a -> RB a
delete x E = E
delete x (T c a y b)
    | member x (T c a y b) = if x < y then (T c (delete x a) y b)
                    else if x > y then (T c a y (delete x b))
                    else removeRoot (T c a y b)
    | otherwise = (T c a y b)


deleteRB :: Ord a => a -> RB a -> RB a
deleteRB x t = blacken (bubble (delete x t))
