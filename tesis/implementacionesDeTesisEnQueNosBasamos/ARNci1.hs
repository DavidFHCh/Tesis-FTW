{-
Kahrs implementación
Extensión a implementación de Okasaki
-}
module ARNci1 (Color(R,B), RB(E,T), member,insert,delete) where

data Color = R | B 
data RB a = E | T Color (RB a) a (RB a)

member :: Int -> RB Int -> Bool
member x E = False
member x (T _ tl y tr)
                    | x<y = member x tl
                    | x>y = member x tr
                    | otherwise = True

insert :: Int -> RB Int -> RB Int
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

balance :: RB Int -> Int -> RB Int -> RB Int
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b

-- Stefhan Kahrs

delete :: Int -> RB Int -> RB Int
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

red :: RB Int -> RB Int
red (T B a x b) = T R a x b
red _ = error "invariance violation"

balleft :: RB Int -> Int -> RB Int -> RB Int
balleft (T R a x b) y c = T R (T B a x b) y c
balleft bl x (T B a y b) = balance bl x (T R a y b)
balleft bl x (T R (T B a y b) z c) = T R (T B bl x a) y (balance b z (red c))

balright :: RB Int -> Int -> RB Int -> RB Int
balright a x (T R b y c) = T R a x (T B b y c)
balright (T B a x b) y bl = balance (T R a x b) y bl
balright (T R a x (T B b y c)) z bl = T R (balance (red a) x b) y (T B c z bl)

app :: RB Int -> RB Int -> RB Int
app E x = x
app x E = x
app (T R a x b) (T R c y d) =
        case app b c of
            T R b' z c' -> T R(T R a x b') z (T R c' y d)
            bc -> T R a x (T R bc y d)
app (T B a x b) (T B c y d) =
        case app b c of
                T R b' z c' -> T R(T B a x b') z (T B c' y d)
                bc -> balleft a x (T B bc y d)
app a (T R b x c) = T R (app a b) x c
app (T R a x b) c = T R a x (app b c)
