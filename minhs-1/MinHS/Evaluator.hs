module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           | Closure VEnv Exp
           deriving (Show)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined -- should not ever be used

evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE E.empty e
evaluate bs = evalE E.empty (Let bs (Var "main"))

evalE :: VEnv -> Exp -> Value
--evalE g e = error $ show e
evalE g (Num n) = I n
evalE g (Con c) = case c of "True" 	-> B True
                            "False"	-> B False
                            "Nil"	-> Nil
                            _ -> error $ show "Error with Con " ++ c
evalE g (App (Prim op) x) = eval1ArgOp op $ evalE g x
evalE g (App (App (Prim op) e1) e2) = eval2ArgOp op (evalE g e1) (evalE g e2)
evalE g (App (App (Con "Cons") x) xs) = Cons n $ evalE g xs
   where 
        I n = evalE g x
evalE g (If e1 e2 e3) = case evalE g e1 of B True  -> evalE g e2
                                           B False -> evalE g e3
evalE g (Var x) = case E.lookup g x of Just v -> v
                                       Nothing -> error $ "Variable out of scope " ++ show x
--Recursively add bindings to environment until we have no more bindings
evalE g (Let [] e2) = evalE g e2
evalE g (Let ((Bind id typ args e1):bs) e2) = 
   case typ of
      Arrow t1 t2 -> case e1 of
	                    --A function in let
                        App a b -> evalE (E.add g (id, e')) (Let bs e2)
                                where
                                     e' = Closure g $ nAryFun $ Letfun (Bind id (Arrow t1 t2) args e1)
                        _ -> evalE (E.add g (id, evalE g e1)) (Let bs e2)
      _ -> evalE (E.add g (id, evalE g e1)) (Let bs e2)
-- nAryFunctions
evalE g (Letfun (Bind id (Arrow t1 t2) (a1:a2:args) e)) = Closure g $ nAryFun $ Letfun (Bind id (Arrow t1 t2) (a1:a2:args) e)
evalE g (Letfun (Bind id (Arrow t1 t2) args e)) = Closure g (Letfun (Bind id (Arrow t1 t2) args e))
--Partial Functions
evalE g (Letfun (Bind id typ [] e)) = evalE (E.add g (id, evalE g e)) e
evalE g (App e1 e2) = case evalE g e1 of
            --Closure g' (Let [Bind id typ args exp1] exp2) -> evalE g' exp1
            --Application of partial function
            Closure g' (Letfun (Bind id (Arrow t1 t2) [] e)) -> evalE g'' (App e e2)
               where
                    g'' = E.add g' (id,  Closure g' (Letfun (Bind id (Arrow t1 t2) [] e)))
            Closure g' (Letfun (Bind id typ (arg:args) e)) -> evalE (E.addAll g' [a1,a2]) e
               where
                    a1 = (id, (Closure g' (Letfun (Bind id typ (arg:args) e))))
                    a2 = (arg, evalE g e2)
            _ -> evalE g e1
evalE g e = error $ "Implement Me! " ++ (show e)

eval1ArgOp :: Op -> Value -> Value
eval1ArgOp Head (Cons x xs) = I x
eval1ArgOp Tail (Cons x xs) = xs
eval1ArgOp Null Nil = B True
eval1ArgOp Null (Cons x xs) = B False
eval1ArgOp Neg (I n) = I (-1 * n)
eval1ArgOp op v = error $ "Error with " ++ show op ++ " " ++ show v

eval2ArgOp :: Op -> Value -> Value -> Value
eval2ArgOp Add  (I v1) (I v2) = I (v1 + v2)
eval2ArgOp Sub  (I v1) (I v2) = I (v1 - v2)
eval2ArgOp Mul  (I v1) (I v2) = I (v1 * v2)
eval2ArgOp Quot (I v1) (I v2) = I (v1 `quot` v2)
eval2ArgOp Gt   (I v1) (I v2) = B (v1 > v2)
eval2ArgOp Ge   (I v1) (I v2) = B (v1 >= v2)
eval2ArgOp Lt   (I v1) (I v2) = B (v1 < v2)
eval2ArgOp Le   (I v1) (I v2) = B (v1 <= v2)
eval2ArgOp Eq   (I v1) (I v2) = B (v1 == v2)
eval2ArgOp Ne   (I v1) (I v2) = B (v1 /= v2)
eval2ArgOp op v1 v2 = error $ "Error with " ++ show op ++ " " ++ show v1 ++ " " ++ show v2 

--recursively puts functions within the nAryfunction to take one argument at a time
nAryFun :: Exp -> Exp
nAryFun (Letfun (Bind id typ [] e)) = Letfun (Bind id typ [] e)
nAryFun (Letfun (Bind id (Arrow t1 t2) (a:args) e)) = Letfun (Bind id (Arrow t1 t2) [a] (nAryFun (Letfun (Bind id t2 args e))))
