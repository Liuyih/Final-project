module Imp where

data Exp
  = Valu Int
  | Get Exp
  | Apply Exp Exp
  | List Int
  | Prim PrimOp Exp Exp
  deriving Show

data Value
  = VInt Int
  | VClosure Exp Env1
  deriving Show

data PrimOp = Additoin | Multipy
  deriving Show

type Env1 = [Value]

eval :: Env1 -> Exp -> Value
eval env1 term = case term of
  Valu n -> env1 !! n
  Get a -> VClosure a env1
  Apply a b ->
    let VClosure c env1' = eval env1 a in
    let v = eval env1 b in
    eval (v : env1') c

  List n -> VInt n
  Prim p a b -> (evalPrim p) (eval env1 a) (eval env1 b)

evalPrim :: PrimOp -> Value -> Value -> Value
evalPrim Additoin (VInt a) (VInt b) = VInt (a + b)
evalPrim Multipy (VInt a) (VInt b) = VInt (a + b)

emptyEnv :: Env1
emptyEnv = []

-- (\x y -> x + y) 10 20
-- test :: Value
-- test = eval emptyEnv $ Apply (Apply (Get (Get (Prim Add1 (Valu 0) (Valu 1)))) (Lit 15)) (Lit 30)
