module

public import LogicLineages.ComputabilityKnowledge.WWClosedAssignment
public import Mathlib.Data.Finset.Basic

@[expose] public section

/-! Exact ground-variable case of WW Definition 2.7. Each name is the sole
component of a distinct ground-type source vector. Total functions χ below
represent partial substitutions on the occurring names: values outside the
independent syntax support are unconstrained and irrelevant by the separate
locality theorem. No full finite-valued-O decision procedure is defined. -/
namespace LogicLineages.ComputabilityKnowledge.WWGroundAdmissibility

open WWOrdinalTermSemantics WWClosedAssignment
open LogicLineages.OrdinalComparison

def support {ι : Type} [DecidableEq ι] : Term ι → Finset ι
  | .var i => {i}
  | .zero | .one | .omega => ∅
  | .add a b | .emul a b | .collapse a b => support a ∪ support b

noncomputable def Admissible {d : Nat} (S : Finset (Fin d)) (χ : Fin d → Term Empty) : Prop :=
  ∀ i ∈ S, B 0 (χ i) ∧ BoundedNorm [χ i]

noncomputable def Comparison {d : Nat} (weak : Bool) (a b : Term (Fin d)) : Prop :=
  ∀ χ : Fin d → Term Empty, Admissible (support a ∪ support b) χ →
    if weak then closedValue (substitute χ a) ≤ closedValue (substitute χ b)
    else closedValue (substitute χ a) < closedValue (substitute χ b)

noncomputable def Equality {d : Nat} (a b : Term (Fin d)) : Prop :=
  ∀ χ : Fin d → Term Empty, Admissible (support a ∪ support b) χ →
    closedValue (substitute χ a) = closedValue (substitute χ b)

noncomputable def NormComparison {d : Nat} (weak : Bool) (a b : Term (Fin d)) : Prop :=
  ∀ χ : Fin d → Term Empty, Admissible (support a ∪ support b) χ →
    if weak then actualOrdinalNorm (closedValue (substitute χ a)) ≤ actualOrdinalNorm (closedValue (substitute χ b))
    else actualOrdinalNorm (closedValue (substitute χ a)) < actualOrdinalNorm (closedValue (substitute χ b))

end LogicLineages.ComputabilityKnowledge.WWGroundAdmissibility
