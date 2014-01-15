module DFIL where

\begin{code}
{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction #-}

import InterpreterLib.Algebras
import InterpreterLib.Functors
import InterpreterLib.SubType

import Comonad
import LVS

import Control.Monad
import Control.Monad.Reader
\end{code}

\begin{code}
sright = S . Right
sleft = S . Left
\end{code}

\section{Non-recursive AST}

We are implementing a modular and composable interpreter for this AST:

\begin{spec}
data Tm
  = V Var | L Var Tm | Tm :@ Tm | Rec Tm
  | N Integer | Tm :+ Tm | Tm :- Tm | Tm :* Tm | Mod Tm Tm
  | Tm :== Tm | Tm :/= Tm | TT | FF | Not Tm | Tm :&& Tm
  | If Tm Tm Tm
  | Next Tm
  | Fby Tm Tm
\end{spec}

However, for using the InterpreterLib, we need the AST in non-recursive
form.

\begin{code}
type Var = String

-- functional constructs
data ExprFun t
    = ELam Var t
    | EVar String
    | EApp t t
    | ERec t
    deriving (Show,Eq)

-- arithmetic
data ExprArith t
    = EInt Integer
    | EAdd t t
    | ESub t t
    | EMult t t
    | EMod t t
    deriving (Show,Eq)

-- booleans
data ExprBool t
    = EBool Bool
    | ENot t
    | EAnd t t
    | EOr t t
    | EEq t t
    | EIf t t t
    deriving (Show,Eq)

-- dataflow
data ExprCausal t
    = EFby t t
    deriving (Show,Eq)
\end{code}

Next we will prepare for the denotations, via algebras, for each of
the constructs.

\begin{code}
data AlgFun t = AlgFun { lam :: ExprFun t -> t
                       , var :: ExprFun t -> t
                       , app :: ExprFun t -> t
                       , rec :: ExprFun t -> t
                       }

data AlgArith t = AlgArith { int :: ExprArith t -> t
                           , add :: ExprArith t -> t
                           , sub :: ExprArith t -> t
                           , mult :: ExprArith t -> t
                           , amod :: ExprArith t -> t
                           }

data AlgBool t = AlgBool { bool :: ExprBool t -> t
                         , bnot :: ExprBool t -> t
                         , band :: ExprBool t -> t
                         , bor :: ExprBool t -> t
                         , eq :: ExprBool t -> t
                         , bif :: ExprBool t -> t
                         }

data AlgCausal t = AlgCausal { fby :: ExprCausal t -> t }
\end{code}

These expression type and algebra types need class instantiations for
functors and algebras, respectively.

\begin{code}
instance Functor ExprFun where
    fmap f (ELam v t) = ELam v (f t)
    fmap f (EVar v) = EVar v
    fmap f (EApp t1 t2) = EApp (f t1) (f t2)
    fmap f (ERec t) = ERec (f t)

instance Algebra ExprFun AlgFun a where
    apply alg x@(ELam _ _) = lam alg x
    apply alg x@(EVar _) = var alg x
    apply alg x@(EApp _ _) = app alg x
    apply alg x@(ERec _) = rec alg x

instance Functor ExprArith where
    fmap f (EInt i) = EInt i
    fmap f (EAdd t1 t2) = EAdd (f t1) (f t2)
    fmap f (ESub t1 t2) = ESub (f t1) (f t2)
    fmap f (EMult t1 t2) = EMult (f t1) (f t2)
    fmap f (EMod t1 t2) = EMod (f t1) (f t2)

instance Algebra ExprArith AlgArith a where
    apply alg x@(EInt _) = int alg x
    apply alg x@(EAdd _ _) = add alg x
    apply alg x@(ESub _ _) = sub alg x
    apply alg x@(EMult _ _) = mult alg x
    apply alg x@(EMod _ _) = amod alg x

instance Functor ExprBool where
    fmap f (EBool b) = EBool b
    fmap f (ENot t) = ENot (f t)
    fmap f (EAnd t1 t2) = EAnd (f t1) (f t2)
    fmap f (EOr t1 t2) = EOr (f t1) (f t2)
    fmap f (EEq t1 t2) = EEq (f t1) (f t2)
    fmap f (EIf tp tt tf) = EIf (f tp) (f tt) (f tf)

instance Algebra ExprBool AlgBool a where
    apply alg x@(EBool _) = bool alg x
    apply alg x@(ENot _) = bnot alg x
    apply alg x@(EAnd _ _) = band alg x
    apply alg x@(EOr _ _) = bor alg x
    apply alg x@(EEq _ _) = eq alg x
    apply alg x@(EIf _ _ _) = bif alg x

instance Functor ExprCausal where
    fmap f (EFby t1 t2) = EFby (f t1) (f t2)

instance Algebra ExprCausal AlgCausal a where
    apply alg x@(EFby _ _) = fby alg x
\end{code}

We also provide some convenience functions for generating terms.

\begin{code}
injFun = inn . sleft
mkELam v t = injFun $ ELam v t
mkEVar = injFun . EVar
mkEApp t1 t2 = injFun $ EApp t1 t2
mkERec = injFun . ERec

injArith = inn . sright . sleft
mkEInt = injArith . EInt
mkEAdd t1 t2 = injArith $ EAdd t1 t2
mkESub t1 t2 = injArith $ ESub t1 t2
mkEMult t1 t2 = injArith $ EMult t1 t2
mkEMod t1 t2 = injArith $ EMod t1 t2

injBool = inn . sright . sright . sleft
mkEBool = injBool . EBool
mkENot = injBool . ENot
mkEAnd t1 t2 = injBool $ EAnd t1 t2
mkEOr t1 t2 = injBool $ EOr t1 t2
mkEEq t1 t2 = injBool $ EEq t1 t2 
mkEIf tc tt tf = injBool $ EIf tc tt tf

injCausal = inn . sright . sright . sright
mkEFby t1 t2 = injCausal $ EFby t1 t2
\end{code}

To complete the construction of our AST/language, we sum the
individual term types to create the language.

\begin{code}
type TermType = ExprFun :$: ExprArith :$: ExprBool :$: ExprCausal

type TermLang = Fix TermType
\end{code}

Enough with the leg-work; here we provide the actual denotation
definitions. But first: a value space.

\begin{code}
data Val
  = I Integer
  | B Bool
  | F ( LV Val -> VSpace Val )

instance Show Val where
    show (I i) = show i
    show (B b) = show b
    show (F _) = "<function value>"
\end{code}

That will not be our final value space; the interpreter will build a
monadic computation that is used to thread the environment (a
comonadic associate list) throughout the denotation functions.

\begin{code}
newtype Env = Env [(String, VSpace Val)]
type VSpace = Reader (LV Env)
runVSpace = runReader
\end{code}

Lastly, some convenience functions for moving in and out of the Val
datatype. These are similar fmap and what fmap2 would be, but also
bring a bit more specificity through patterns.

\begin{code}

onX :: (a -> Val, Val -> a) -> (a -> a) -> Val -> Val
onX (inX,outX) op ix = inX $ op x
    where x = outX ix

onX2 :: (a -> Val, Val -> a) -> (a -> a -> a) -> Val -> Val -> Val
onX2 (inX,outX) op ix iy = inX $ x `op` y
    where x = outX ix
          y = outX iy

onI2 = onX2 (I, \(I a) -> a)
onB = onX (B, \(B a) -> a)
onB2 = onX2 (B, \(B a) -> a)

\end{code}

This brings us to the denotation functions for each functor.

\begin{code}
phiLam (ELam v t) =
    do denv <- ask
       let repair (a, Env env) = Env $ (v, return a) : env
           extendDenv d = cmap repair (czip d denv)
       return $ F ( \d -> return $ runVSpace t (extendDenv d) )

phiVar (EVar v) =
    do let unJust (Just x) = x
           get (Env env) = unJust $ lookup v env
       denv <- ask
       get (counit denv)

phiApp (EApp t1 t2) =
    do denv <- ask
       (F f) <- t1
       f $ cobind (runVSpace t2) denv

phiRec tm@(ERec t) =
    do denv <- ask
       (F f) <- t
       f $ cobind (runVSpace (phiRec tm)) denv

phiInt (EInt i) = return $ I i
phiAdd (EAdd x y) = liftM2 (onI2 (+)) x y
phiSub (ESub x y) = liftM2 (onI2 (-)) x y
phiMult (EMult x y) = liftM2 (onI2 (*)) x y
phiMod (EMod x y) = liftM2 (onI2 mod) x y

phiBool (EBool b) = return $ B b
phiNot (ENot x) = liftM (onB not) x
phiAnd (EAnd x y) = liftM2 (onB2 (&&)) x y
phiOr (EOr x y) = liftM2 (onB2 (||)) x y
vEq (B x) (B y) = B $ x == y
vEq (I x) (I y) = B $ x == y
phiEq (EEq x y) = liftM2 vEq x y

phiIf (EIf b t f) =
    do denv <- ask
       (B b') <- b
       if b' then t else f

phiFby (EFby t1 t2) =
    do denv <- ask
       v1 <- t1
       return $ v1 `fbyLV` cobind (runVSpace t2) denv

\end{code}

Finally we glue all of the algebras together to form the composite
algebra, and with the addition of the catamorphism, the evalutation function.

\begin{code}
termAlg = (AlgFun phiLam phiVar phiApp phiRec)
          @+@ (AlgArith phiInt phiAdd phiSub phiMult phiMod)
          @+@ (AlgBool phiBool phiNot phiAnd phiOr phiEq phiIf)
          @+@ (AlgCausal phiFby)

emptyS = (Env []) :< emptyS

eval tm = runLV (runVSpace (cata termAlg tm)) emptyS
\end{code}

Some example ASTs.

\begin{code}
pos :: TermLang
pos = mkERec (mkELam "pos" ((mkEInt 0) `mkEFby` ( (mkEVar "pos") `mkEAdd` (mkEInt 1) )))

test = mkERec (mkELam "x" (mkEInt 0))
test2 = (mkELam "x" ((mkEVar "x") `mkEAdd` (mkEInt 1))) `mkEApp` (mkEInt 4)
test3 = test2 `mkEFby` (mkEInt 1)
\end{code}
