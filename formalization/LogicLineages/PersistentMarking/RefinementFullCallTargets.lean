import LogicLineages.PersistentMarking.RefinementSyntaxTargets
namespace LogicLineages.PersistentMarking.RefinementFullCallTargets
open Spine NameBridge

/-- Only the accumulator changes; original-spine branch selection is fixed. -/
def AccumulatorSuccess : Prop := ∀ q args vs ws r,
  applyAux q args vs = some r → ∃ r', applyAux q args ws = some r'

/-- An outer literal free variable is removed beyond a retained inner block.
This is deliberately not an arbitrary-value substitution composition law. -/
def FreeOuterBlock : Prop := ∀ vs d σ x q,
  substitute vs d (substitute (.cons (.free σ x) .nil) (d + vs.length) q) =
    substitute (vs.append (.cons (.free σ x) .nil)) d q

def FreeOuterBlockArgs : Prop := ∀ vs d σ x qs,
  substituteArgs vs d (substituteArgs (.cons (.free σ x) .nil) (d + vs.length) qs) =
    substituteArgs (vs.append (.cons (.free σ x) .nil)) d qs

/-- Exact actual auxiliary-call invariant, preserving original variable
blocking even if the original bound variable is replaced by a free one. -/
def FreeOpeningAux : Prop := ∀ σ x q args vs,
  applyAux (substitute (.cons (.free σ x) .nil) vs.length q) args vs =
    applyAux q args (vs.append (.cons (.free σ x) .nil))

/-- Only literal free first arguments; no general staged associativity. -/
def FreeOpeningCall : Prop := ∀ σ x q args,
  apply (.lam σ q) (.cons (.free σ x) args) = apply (openBody σ x q) args

end LogicLineages.PersistentMarking.RefinementFullCallTargets
