








-----------Constructores Inteligentes 2---------
module ABRN2
where

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


                
