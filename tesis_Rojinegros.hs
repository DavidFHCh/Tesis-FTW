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
--minimo del arbol
mLeft :: AB a -> a
mLeft (T E x r) = r
mLeft (T l x r) = mLeft l
