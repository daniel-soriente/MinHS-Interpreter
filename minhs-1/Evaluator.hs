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
           | Partial Exp
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
evalE g (App (App (Con "Cons") x) xs) = Cons n $ extractClosure $ evalE g xs
   where 
        I n = extractClosure $ evalE g x
evalE g (App (Prim op) e) = eval1ArgOp op $ extractClosure $ evalE g e
evalE g (App (App (Prim op) e1) e2) = eval2ArgOp op (extractClosure (evalE g e1)) (extractClosure (evalE g e2))
evalE g (If e1 e2 e3) = case extractClosure (evalE g e1) of B True  -> evalE g e2
                                                            B False -> evalE g e3
evalE g (Var x) = case E.lookup g x of Just v -> v
                                       Nothing -> error $ "Variable not in environment " ++ show x
--Multiple let bindings
evalE g (Let binds e) = evalE (newEnv g binds) e
   where
        newEnv :: VEnv -> [Bind] -> VEnv
        newEnv g [] = g
		--Functions with one argument
        newEnv g ((Bind id (Arrow t1 t2) (arg:[]) e):bs) = newEnv (E.add g (id, e')) bs
           where
                e' = Closure g (Let [Bind id (Arrow t1 t2) (arg:[]) e] e)
        newEnv g ((Bind id (Arrow t1 t2) (arg:args) e):bs) = newEnv (E.add g (id, e')) bs
           where
                e' = Closure g (Let [Bind id (Arrow t1 t2) [arg] e''] e'')
                e'' = nAryFun 1 $ Bind id t2 (args) e
        newEnv g ((Bind id typ arg e):bs) = newEnv (E.add g (id, evalE g e)) bs
--Partial Primops
evalE g (Letfun (Bind id (Arrow t1 t2) [] e)) = Closure (E.add g (id, (Partial e))) (Letfun (Bind id (Arrow t1 t2) [] e))
--nAry Functions
evalE g (Letfun (Bind id typ (arg1:arg2:args) e)) = Closure (E.add g (id, evalE g e')) (Letfun (Bind id' typ' arg' e'))
   where
        (Letfun (Bind id' typ' arg' e')) = nAryFun 1 $ Bind id typ (arg1:arg2:args) e
evalE g (Letfun (Bind id typ arg e1)) = Closure (E.add g (id, evalE g e1)) (Letfun (Bind id typ arg e1))
--Function application
evalE g (App e1 e2) = case evalE g e1 of 
            Closure g' (Let [Bind id typ (arg:args) exp1] exp2) -> evalE (E.add g' (arg, evalE g e2)) exp1
            Closure g' (Letfun (Bind id (Arrow t1 t2) [] exp)) -> evalE g' (App exp e2)
            Closure g' (Letfun (Bind id typ (arg:args) exp)) -> evalE (E.addAll g' [a1,a2]) exp
               where
                    a1 = (id, (Closure g' (Letfun (Bind id typ (arg:args) exp))))
                    a2 = (arg, evalE g e2)
            _ -> error $ show $ evalE g e1
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

--Create a variable that is not used in the environment
newVariable :: VEnv -> String -> String
newVariable g s = case E.lookup g s of Just a -> newVariable g (s ++ "'")
                                       Nothing -> s

--creates new expression for n-ary functions
--Puts letfun expressions within letfun expressions for each parameter
nAryFun :: Int -> Bind -> Exp
nAryFun n (Bind id typ (arg:[]) e) = case typ of (Arrow t1 (Arrow t2 t3)) -> (Letfun (Bind (id ++ show n) typ [arg] e'))
                                                    where
                                                         e' = Letfun (Bind (id ++ show (n+1)) (Arrow t2 t3) [] e)
                                                 _ -> (Letfun (Bind (id ++ show n) typ [arg] e))
nAryFun n (Bind id typ (arg:args) e) | (n == 1) = (Letfun (Bind id typ [arg] e'))
									 | otherwise = (Letfun (Bind (id ++ show n) typ [arg] e'))
								          where
											   (Arrow t1 t2) = typ
											   e' = (nAryFun (n+1) (Bind id t2 args e))
											 
--In the case of a function just returning an interger or list
--eg. f = 1
extractClosure :: Value -> Value
--extractClosure (Closure g (Let [Bind id typ [] exp1] exp2)) = evalE g exp1
extractClosure (Closure g (Letfun (Bind id typ [] exp))) = evalE g exp
extractClosure a = a
