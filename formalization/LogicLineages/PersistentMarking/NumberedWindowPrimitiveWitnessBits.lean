import LogicLineages.PersistentMarking.NumberedWindowRules
import LogicLineages.PersistentMarking.NumberedWindowLiteralEquality
import Init.Data.List.Perm

namespace LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessBits
open NumberedWindowSyntax NumberedWindowLiteralEquality

/-- A literal original mark decrease, allowing only a common initial
lambda prefix and retaining every unchanged head field and occurrence. -/
def markBit : NTerm → NTerm → Bool
  | .ordinary f bs, .numbered g τ _ bt .nil =>
    decide (f = g) && decide (τ = f.result) && argsEq bs bt
  | .numbered f τ k bs es, .numbered g ρ l bt et =>
    decide (f = g) && decide (τ = ρ) && decide (l < k) &&
      argsEq bs bt && argsEq es et
  | .lam σ Q, .lam ρ R => decide (σ = ρ) && markBit Q R
  | _, _ => false

/-- Exactly the literal syntax equality test, not primary equivalence.
The ordinary list-permutation algorithm keeps occurrence multiplicity. -/
def literalTermBEq : BEq NTerm := ⟨termEq⟩

def permBit (xs ys : List NTerm) : Bool :=
  @List.isPerm NTerm literalTermBEq xs ys

/-- Explicit finite witness: the retained, removed, and inserted lists
of occurrences, with both literal permutations checked independently. -/
structure ReplacementWitness where
  kept : List NTerm
  removed : List NTerm
  added : List NTerm

/-- The checker does not choose or search for a partition. Only the finite
dominator search over the supplied removed list is performed. -/
def replacementBit (source target : NArgs) (w : ReplacementWitness) : Bool :=
  permBit source.toList (w.kept ++ w.removed) &&
    permBit target.toList (w.kept ++ w.added) &&
    !w.removed.isEmpty &&
    w.added.all (fun a => w.removed.any (fun b => markBit b a))

end LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessBits
