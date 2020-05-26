module Design where
import Data.Map (Map,fromList,lookup,insert)
import Data.Maybe (fromJust)
import Prelude hiding (lookup)
import Imp


-- | Example program 1
ex1 :: Prog
ex1 = P [("sum",TInt),("n",TInt)]
      (Block [
        Set "sum" (Lit 0),
        Set "n" (Lit 100),
        While (Equ (Ref "n") (Lit 100))
        (Block [Set "sum" (Add (Ref "sum") (Ref "n"))])
      ])


test :: Value
test = eval emptyEnv $ Apply (Apply (Get (Get (Prim Additoin (Valu 0) (Valu 1)))) (List 15)) (List 30)


ex2 :: Prog
ex2 = P [("x",TInt),("y",TInt),("z",TInt)]
     (Block [
       Set "x" (Lit 0),
       Set "y" (Lit 1),
       Set "z" (Lit 2),
       If (Gt (Ref "x")(Ref "y")) (Set "x" (Lit 2)) (Set "y" (Lit 3)),
       Set "z" (Lit 2),
       While (LTE (Ref "y") (Ref "z"))
       (Block [
        Set "z" (Sub (Ref "z") (Lit 1)),
        Set "y" (Div (Ref "y") (Lit 2))
       ])
      ])

ex3 :: Prog
ex3 = P [("sum",TInt),("n",TInt)]
     (Block [
       Set "sum" (Lit 0),
       Set "n" (Lit 1),
       While (Equ (Ref "n") (Lit 100))
       (Block [
        Set "sum" (Gt (Ref "n") (Lit 50))
        ])
      ])



-- | String interaction

help = do
    putStrLn ("--------------------Function------------------ " ++ "\n" ++ "1. addition"++ "\n" ++ "2. subtraction"++ "\n"++ "3. multiply"++ "\n"++ "4. division"++ "\n"++ "5. Less Than"++ "\n"++ "6. Great than"++ "\n" ++ "7. Equal"++ "\n" ++ "8. Boolean negation"++ "\n")


len = do
        putStrLn ( "/*Length of string*/" )
        len_string <- getLine
        putStrLn $ "Len: " ++ show (length len_string)


-- | Variables.
type Var = String

-- | Abstract syntax of expressions.

data Expr = Lit Int        -- literal integer
          | Add Expr Expr  -- integer addition
          | Sub Expr Expr  -- integer sub
          | Mul Expr Expr  -- integer multiply
          | Div Expr Expr  -- integer division
          | LTE Expr Expr  -- less than
          | Gt Expr Expr   -- great than
          | Equ Expr Expr  -- equal
          | Not Expr       -- boolean negation
          | Ref Var        -- variable reference
          | Fun Var Expr    -- anonymous function w/ one argument
          | App Expr Expr    -- function application
  deriving (Eq,Show)


-- | Abstract syntax of statements.

data Stmt = Set Var Expr
          | If Expr Stmt Stmt
          | While Expr Stmt
          | For Expr Expr Stmt
          | Block [Stmt]
  deriving (Eq,Show)

-- | Abstract syntax of types.

data Type = TInt
            | TBool
            | TF Var Expr
  deriving (Eq,Show)

-- | Abstract syntax of declarations.

type Decl = (Var,Type)

-- | Abstract syntax of programs.

data Prog = P [Decl] Stmt
  deriving (Eq,Show)


--
-- * Type
--

type Env a = Map Var a

typeExpr :: Expr -> Env Type -> Maybe Type
typeExpr (Lit _)   _ = Just TInt
typeExpr (Add l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TInt
                         _                      -> Nothing
typeExpr (Sub l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TInt
                         _                      -> Nothing
typeExpr (Mul l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TInt
                         _                      -> Nothing
typeExpr (Div l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TInt
                         _                      -> Nothing
typeExpr (Gt l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TBool
                         _                      -> Nothing
typeExpr (Equ l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TBool
                         _                      -> Nothing


typeExpr (LTE l r) m = case (typeExpr l m, typeExpr r m) of
                         (Just TInt, Just TInt) -> Just TBool
                         _                      -> Nothing
typeExpr (Not e)   m = case typeExpr e m of
                         Just TBool -> Just TBool
                         _          -> Nothing
typeExpr (Ref v)   m = lookup v m

typeExpr (Fun x e)   m = Just (TF x e)

typeExpr (App l r)   m = case (typeExpr l m, typeExpr r m) of
                       (Just (TF x e), Just v) -> typeExpr e (insert x v m)
                       _ -> Nothing


typeStmt :: Stmt -> Env Type -> Bool
typeStmt (Set v e)   m = case (lookup v m, typeExpr e m) of
                            (Just tv, Just te) -> tv == te
                            _ -> False
typeStmt (If c st se) m = case typeExpr c m of
                            Just TBool -> typeStmt st m && typeStmt se m
                            _ -> False
typeStmt (While c sb) m = case typeExpr c m of
                            Just TBool -> typeStmt sb m
                            _ -> False
--typeStmt (For c d st) m = case (typeExpr c m, typeExpr d m) of
--                            (Just TInt, Just TInt) -> typeStmt st m
  --                          _ -> False
typeStmt (Block ss)   m = all (\s -> typeStmt s m) ss


typeProg :: Prog -> Bool
typeProg (P ds s) = typeStmt s (fromList ds)


--
-- * Semantics
--

-- | The basic values in our language.
type Val = Either Int Bool


evalExpr :: Expr -> Env Val -> Val
evalExpr (Lit i)   _ = Left i
evalExpr (Add l r) m = Left (evalInt l m + evalInt r m)
evalExpr (Sub l r) m = Left (evalInt l m - evalInt r m)
evalExpr (Mul l r) m = Left (evalInt l m * evalInt r m)
evalExpr (Div l r) m = Left (evalInt l m `div` evalInt r m)
evalExpr (LTE l r) m = Right (evalInt l m < evalInt r m)
evalExpr (Gt l r)  m = Right (evalInt l m > evalInt r m)
evalExpr (Equ l r) m = Right (evalInt l m == evalInt r m)
evalExpr (Not e)   m = Right (not (evalBool e m))
evalExpr (Ref x)   m = case lookup x m of
                         Just v  -> v
                         Nothing -> error "internal error: undefined variable"
evalExpr (Fun x e) m = evalExpr e m
-- evalExpr (App l r) m = evalExpr r m





evalInt :: Expr -> Env Val -> Int
evalInt e m = case evalExpr e m of
                Left i  -> i
                Right _ -> error "internal error: expected Int got Bool"


evalBool :: Expr -> Env Val -> Bool
evalBool e m = case evalExpr e m of
                 Right b -> b
                 Left _  -> error "internal error: expected Bool got Int"


evalStmt :: Stmt -> Env Val -> Env Val
evalStmt (Set x e)   m = insert x (evalExpr e m) m
evalStmt (If c st se) m = if evalBool c m
                          then evalStmt st m
                          else evalStmt se m
evalStmt (While c sb) m = if evalBool c m
                          then evalStmt (While c sb) (evalStmt sb m)
                          else m
evalStmt (For c d st) m = if (evalInt c m < evalInt d m)
                          then evalStmt (While (Gt (Sub d c) (Lit 0)) st) (evalStmt st m)
                          else m
evalStmt (Block ss)   m = evalStmts ss m


evalStmts :: [Stmt] -> Env Val -> Env Val
evalStmts []     m = m
evalStmts (s:ss) m = evalStmts ss (evalStmt s m)


evalProg :: Prog -> Env Val
evalProg (P ds s) = evalStmt s m
  where
    m = fromList (map (\(x,t) -> (x, init t)) ds)
    init TInt  = Left 0
    init TBool = Right False


startProg :: Prog -> Maybe (Env Val)
startProg p = if typeProg p then Just (evalProg p)
                          else Nothing
