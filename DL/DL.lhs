\documentclass[10pt]{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%format phi = "\Varid{\phi}"
%format phi1 = "\Varid{\phi_1}"
%format phi2 = "\Varid{\phi_2}"
%format phi3 = "\Varid{\phi_3}"
%format eval1 = "\Varid{eval}_1"
%format eval2 = "\Varid{eval}_2"
%format eval3 = "\Varid{eval}_3"
%format eval4 = "\Varid{eval}_4"
%format Expr1 = "\Varid{Expr}_1"
%format Expr2 = "\Varid{Expr}_2"
%format Expr3 = "\Varid{Expr}_3"
%format E1 = "\Varid{E}_1"
%format E2 = "\Varid{E}_2"
%format E3 = "\Varid{E}_3"
%format evalE = "\Varid{eval}_E"
%format mapE = "\Varid{map}_E"
%format phiE = "\Varid{\phi}_E"
%format test0 = "\Varid{test}_0"
%format test1 = "\Varid{test}_1"
%format test2 = "\Varid{test}_2"
%format test3 = "\Varid{test}_3"
%format test4 = "\Varid{test}_4"
%format test5 = "\Varid{test}_5"
%format test6 = "\Varid{test}_6"
%format test7 = "\Varid{test}_7"
%format test8 = "\Varid{test}_8"
%format test9 = "\Varid{test}_9"
%format test10 = "\Varid{test}_{10}"

\usepackage{fullpage}
\usepackage{alltt}

\bibliographystyle{plain}

\parskip=\medskipamount
\parindent=0pt

\title{Constructing a Comonadic Stream Processor Using
  InterpreterLib:\\ Putting the pieces together}

\author{\emph{Uk'taad B'mal} \\
  The University of Kansas - ITTC \\
  2335 Irving Hill Rd, Lawrence, KS 66045 \\
  \texttt{lambda@@ittc.ku.edu}}

\begin{document}

\maketitle

\begin{abstract}
  Abstract goes here...
\end{abstract}

\section{Introduction}

What we do in this report is take all of our interpreter pieces and
put them together to write a stream transformer.  First we define a
simple expression language that supports lambda abstraction,
conditionals, Booleans and integers.  This language is in every way
identical to earlier languages written with |InterpreterLib|.  It is
modular and monadic in nature.  We will extend the abstract syntax
elements from |InterpreterLib| to include an |fby| operation defining
the dataflow concept of ``followed by''.  To interpret |fby|, we must
introduce data flow semantics.  We choose to do this using a comonad
as defined by Uustalu and Vene~\cite{Uustalu:05:The-Essence-of-}.  In
effect, we are taking a simple lambda language and inserting it into a
comonad to create a stream transformer.

If we take this new stream transformer and evaluate it using the |Id|
comonad, the resulting system is simply the original interpreter.  The
|Id| comonad has no concept of past or future and thus processes a
single value stream.

Moving to the |LV| or |Causal| comonad allows us to record the past as
stream elements are processes.  Specifically, the |LV| comonad accepts
an input stream and produces a list representing past values.  This is
in effect a discrete event simulator where the events are input from
the input stream.

Finally, moving to the |LVS| comonad allows us to move backwards and
forwards along the input and output streams.  |LVS| gives us a
simulator that allows stopping, reversing and restarting during
execution.

The ultimate question has to be why we care about this.  In a way, we
have created the ultimate in modular interpreter by introducing
temporal events.  The ordering of events in the input stream defines
the temporal flow of the resulting simulator.  |Id| gives us an
interpreter because there is no temporal orderin.  |LV| gives us
causal simulation because we only move forward through the input
stream.  |LVS| gives us both backward and forward reference providing
the most flexible temporal model.  All this \emph{without changing the
interpreter}.  We can change the time reference, explore branching
time, or eliminate time altogether by changing the comonad use for
evaluation or by changing the nature of the input stream.  Thus, we
have created a siulator where time is simply one aspect of the
composable interpreter like any other.

\section{Imports and Options}

The interpreter imports virtually everything we have written to
support interpreter construction.  First the |InterpreterLib| package
is loaded along with terms used in our abstract syntax.  Note the
import of |Causal|, a new module providing the |Fby| expression
syntax.  The |Comonad| packages are then loaded to construct the
comonad that sequences interpretation.  Finally, the |Monad| modules
are loaded to construct the interpreter monadically.

\begin{code}

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
\end{code}

\section{Term Space}

The term language is a trivial language with the addition of a data
flow construct.  The first five term types define a trivial lambda
language.  (See earlier documentation of |InterpreterLib| if this is
confusing.)  The final term adds the followed by syntax to support
moving interpretation through time.  As usual, the full language is
the fixed point of the non-recursive AST structure.

\begin{code}
type TermType = (LambdaTerm ()) :$:
                VarTerm :$:
                FixTerm :$:
                ArithTerm :$:
                IfTerm :$:
                Causal

type TermLang = Fix TermType
\end{code}

\section{Value Space}

The value space of tis interpreter includes integers, booleans and
lambdas.  There is no need for a non-recursive representation here.

\begin{code}
data Val
  = I Int
  | B Bool
  | F ( LV Val -> VSpace Val )

instance Show Val where
    show (I i) = show i
    show (B b) = show b
    show (F _) = "<function value>"
\enb{code}

\section{Environment}

The environment of this interpreter is...

\begin{code}
type VSpace = Reader (LV Env)
newtype Env = Env [(String, VSpace Val)]
runVSpace = runReader

\end{code}

\section{The Semantic Algebra}

At this point we defined the explicit semantic algebra used by the
intepreter.  Functions for each language construct are defined first
and then assembpled into the explicit algebra.

\subsection{Lambda Evaluation}

Lambda values are functions that map from a comonadic enviornment to
the result of evaluating the abstracted expressions.  A lambda
application simply applies the lambda value to the environment it is
to be evaluated in.  The formation of the lambda value is where we see
the comonadic environment and the monadic evaluation function
interact.  Here, we see the |Reader| monad used to implement the
behavior of a locally defined variable.  At the same time, |cmap|,
|repair| and |czip| facilite the environment change over the entire
comonad. 

\begin{code}
phiLam (Lam v () t) = 
    do denv <- ask
       let repair (a, Env env) = Env $ (v, return a) : env
           extendDenv d = cmap repair (czip d denv)
       return $ F (\d -> local (const (extendDenv d)) t)

phiLam (App t1 t2) = 
    do denv <- ask
       (F f) <- t1
       f $ cobind (runVSpace t2) denv
\end{code}

\subsection{Fixed Point Evaluation}

Fixed point evaluation implements the general fixed point definition
|fix f = f (fix f).  The last terms in the |do| expression perform
exactly this evaluation.  The term, |t|, is deconstructed and |f| is
applied to the result of evaluating |fix f|.

\begin{code}
phiFix tm@(FixTerm t) =
    do denv <- ask
       (F f) <- t
       f $ cobind (runVSpace (phiFix tm)) denv
\end{code}

\subsection{Variable Evaluation}

Variable evaluation again sees the comonad interacting with the
evaluator.  |counit| extracts the current environment while monadic
expressions 

\begin{code}
phiVar :: (VarTerm (VSpace Val)) ->  (VSpace Val)
phiVar (VarTerm v) =
    do let unJust (Just x) = x
           get (Env env) = unJust $ lookup v env
       denv <- ask
       get (counit denv)


lift2Int2 op (I x) (I y) = I $ x `op` y

lift2Int2Bool2 op (I x) (I y) = B $ x `op` y
\end{code}

\subsection{Arithmetic Expression Evaluation}

\begin{code}
phiArith (Add x y) = liftM2 (lift2Int2 (+)) x y
phiArith (Sub x y) = liftM2 (lift2Int2 (-)) x y
phiArith (Mult x y) = liftM2 (lift2Int2 (*)) x y
phiArith (Div x y) = liftM2 (lift2Int2 div) x y
phiArith (NumEq x y) = liftM2 (lift2Int2Bool2 (==)) x y
phiArith (Num i) = return $ I i
\end{code}

\subsection{IF Term Evaluation}

\begin{code}
phiIf (IfTerm b t f) =
    do denv <- ask
       (B b') <- b
       if b' then t else f

phiIf TrueTerm = return (B True)
phiIf FalseTerm = return (B False)
\end{code}

\subsection{Followed By Evaluation}

\begin{code}
phiCausal (FBy t1 t2) =
    do denv <- ask
       v1 <- t1
       return $ v1 `fbyLV` cobind (runVSpace t2) denv
\end{code}

\subsection{Forming The Semantic Algebra}

\begin{code}
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
\end{code}

\bibliography{sldg}

\end{document}

