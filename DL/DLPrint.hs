module DLPrint where

{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction -fallow-overlapping-instances #-}

import InterpreterLib.Algebras
import InterpreterLib.Functors
import InterpreterLib.SubType

import InterpreterLib.Terms.Arith
import InterpreterLib.Terms.LambdaTerm
import InterpreterLib.Terms.FixTerm
import InterpreterLib.Terms.IfTerm

import DL(TermLang,TermType)
import Causal


import Text.PrettyPrint


phiLam (Lam v () t) = parens $ text "\\" <> text v <> text " -> " <> t

phiLam (App t1 t2) = parens (t1 <> t2)



phiFix tm@(FixTerm t) = text "fix" <+> t

phiVar :: VarTerm Doc -> Doc
phiVar (VarTerm v) = text v

phiArith (Add x y) = mkop "+" x y
phiArith (Sub x y) = mkop "-" x y
phiArith (Mult x y) = mkop "*" x y
phiArith (Div x y) = mkop "/" x y
phiArith (NumEq x y) = mkop "==" x y
phiArith (Num i) = integer $ toInteger i 

mkop op x y = x <+> (text op) <+> y

phiIf (IfTerm b t f) =
  (text "if") <+> b $$ 
  (text "then") <+> t $$
  (text "else") <+> f 
 

phiIf TrueTerm = text "true"
phiIf FalseTerm = text "false"

phiCausal (FBy t1 t2) =
  t1 <+> (text "fby") <+> t2

alg = (mkAlgebra phiLam) @+@
      (mkAlgebra phiVar) @+@ 
      (mkAlgebra phiFix) @+@
      (mkAlgebra phiArith) @+@
      (mkAlgebra phiIf) @+@
      (mkAlgebra phiCausal)


printAlg = cata alg
