module Causal where
import InterpreterLib.Functors
import InterpreterLib.Algebras
 
data Causal carrier = FBy carrier carrier
 
data CausalAlgebra carrier = CausalAlgebra{applyFBy ::
                                           Causal carrier -> carrier}
 
instance Functor Causal where
        fmap f (FBy arg0 arg1) = FBy (f arg0) (f arg1)
 
instance Algebra Causal CausalAlgebra carrier where
        apply alg t@(FBy _ _) = applyFBy alg t
 
instance AlgebraBuilder Causal ((->) (Causal carrier) carrier)
         CausalAlgebra carrier where
        mkAlgebra phi = CausalAlgebra phi
makeFBy arg0 arg1 = toS (FBy arg0 arg1)
 
data AntiCausal carrier = Next carrier
 
data AntiCausalAlgebra carrier = AntiCausalAlgebra{applyNext ::
                                                   AntiCausal carrier -> carrier}
 
instance Functor AntiCausal where
        fmap f (Next arg0) = Next (f arg0)
 
instance Algebra AntiCausal AntiCausalAlgebra carrier where
        apply alg t@(Next _) = applyNext alg t
 
instance AlgebraBuilder AntiCausal
         ((->) (AntiCausal carrier) carrier) AntiCausalAlgebra carrier where
        mkAlgebra phi = AntiCausalAlgebra phi
makeNext arg0 = toS (Next arg0)