import LogicLineages.PersistentMarking.NumberedWindowSyntax

namespace LogicLineages.PersistentMarking.NumberedWindowExternalBindingNaturalityTargets
open NumberedWindowSyntax

def SubstituteAfterShift : Prop :=
  (∀ values d n c (q : NTerm), c ≤ d →
    substitute values (d+n) (shift n c q) = shift n c (substitute values d q)) ∧
  ∀ values d n c (xs : NArgs), c ≤ d →
    substituteArgs values (d+n) (shiftArgs n c xs) = shiftArgs n c (substituteArgs values d xs)

def SubstituteBeta : Prop :=
  ∀ values d a body, substitute values d (substitute (.cons a .nil) 0 body) =
    substitute (.cons (substitute values d a) .nil) 0 (substitute values (d+1) body)

def SubstituteFreshBody : Prop :=
  ∀ values d f σ τ k bs es, substitute values (d+1) (openNumbered f σ τ k bs es) =
    openNumbered f σ τ k (substituteArgs values d bs) (substituteArgs values d es)

end LogicLineages.PersistentMarking.NumberedWindowExternalBindingNaturalityTargets
