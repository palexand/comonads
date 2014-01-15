module DL where

{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction -fallow-overlapping-instances #-}

import InterpreterLib.Algebras
import InterpreterLib.Functors
import InterpreterLib.SubType

import InterpreterLib.Terms.Arith
import InterpreterLib.Terms.LambdaTerm
import InterpreterLib.Terms.FixTerm
import InterpreterLib.Terms.IfTerm

import Causal

import Comonad
import Comonad.LV
import Comonad.LVS
import Comonad.Stream

import Control.Monad
import Control.Monad.Reader

type TermType = (LambdaTerm ()) :$:
                VarTerm :$:
                FixTerm :$:
                ArithTerm :$:
                IfTerm :$:
                Causal


-- type TermType = ExprFun :$: ExprArith :$: ExprBool :$: ExprCausal
type TermLang = Fix TermType


data Val
  = I Int
  | B Bool
  | F ( LV Val -> VSpace Val )

instance Show Val where
    show (I i) = show i
    show (B b) = show b
    show (F _) = "<function value>"

newtype Env = Env [(String, VSpace Val)]
type VSpace = Reader (LV Env)
runVSpace = runReader


phiLam (Lam v () t) = 
    do denv <- ask
       let repair (a, Env env) = Env $ (v, return a) : env
           extendDenv d = cmap repair (czip d denv)
       return $ F (\d -> local (const (extendDenv d)) t)

phiLam (App t1 t2) = 
    do denv <- ask
       (F f) <- t1
       f $ cobind (runVSpace t2) denv


phiFix tm@(FixTerm t) =
    do denv <- ask
       (F f) <- t
       f $ cobind (runVSpace (phiFix tm)) denv

phiVar :: (VarTerm (VSpace Val)) ->  (VSpace Val)
phiVar (VarTerm v) =
    do let unJust (Just x) = x
           get (Env env) = unJust $ lookup v env
       -- asks (get . counit)
       denv <- ask
       get (counit denv)


lift2Int2 op (I x) (I y) = I $ x `op` y

lift2Int2Bool2 op (I x) (I y) = B $ x `op` y

phiArith (Add x y) = liftM2 (lift2Int2 (+)) x y
phiArith (Sub x y) = liftM2 (lift2Int2 (-)) x y
phiArith (Mult x y) = liftM2 (lift2Int2 (*)) x y
phiArith (Div x y) = liftM2 (lift2Int2 div) x y
phiArith (NumEq x y) = liftM2 (lift2Int2Bool2 (==)) x y
phiArith (Num i) = return $ I i

phiIf (IfTerm b t f) =
    do denv <- ask
       (B b') <- b
       if b' then t else f

phiIf TrueTerm = return (B True)
phiIf FalseTerm = return (B False)

phiCausal (FBy t1 t2) =
    do denv <- ask
       v1 <- t1
       return $ v1 `fbyLV` cobind (runVSpace t2) denv

alg = (mkAlgebra phiLam) @+@
      (mkAlgebra phiVar) @+@ 
      (mkAlgebra phiFix) @+@
      (mkAlgebra phiArith) @+@
      (mkAlgebra phiIf) @+@
      (mkAlgebra phiCausal)


emptyS = (Env []) :< emptyS

eval tm = runLV (runVSpace (cata alg tm)) emptyS


pos :: TermLang
pos = makeFixTerm (makeLam "pos" () ((makeNum 0) `makeFBy` ( (makeVarTerm "pos") `makeAdd` (makeNum 1) )))
