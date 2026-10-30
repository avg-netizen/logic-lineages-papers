module

public import LogicLineages.ComputabilityKnowledge.WWGroundAdmissibility

@[expose] public section

/-! The independent-ground-name restriction of the original C_i classes in
WW Definition 2.9 (C, not C^x). Ground variables have only component 0.
The lift rule therefore has no x-freeness condition, exactly as stipulated
for C. The collapse side condition uses the actual source norm and original
occurring-name admissible substitutions. Extraction of the finite argument
of F2 is justified by the separate C→B and finite-C0 theorems. -/
namespace LogicLineages.ComputabilityKnowledge.WWGroundClasses

open WWOrdinalTermSemantics WWClosedAssignment WWGroundAdmissibility
open LogicLineages.OrdinalComparison

noncomputable def CollapseCondition {d : Nat} (f g : Term (Fin d)) : Prop :=
  ∀ χ : Fin d → Term Empty, Admissible (support f ∪ support g) χ →
    actualOrdinalNorm (closedValue (substitute χ f)) ≤
      fastControl 2 (closedValue (substitute χ g)).card.toNat

inductive C (d : Nat) : Nat → Term (Fin d) → Prop where
  | one (i : Nat) : C d i .one
  | omega (i : Nat) (hi : 1 ≤ i) : C d i .omega
  | groundVar (j : Fin d) : C d 0 (.var j)
  | add {i : Nat} {f g : Term (Fin d)} : C d i f → C d i g → C d i (.add f g)
  | emul {i : Nat} {f g : Term (Fin d)} : 1 ≤ i → C d (i + 1) f → C d i g → C d i (.emul f g)
  | collapse {f g : Term (Fin d)} : C d 1 f → C d 0 g → CollapseCondition f g → C d 0 (.collapse f g)
  | lift {i : Nat} {h : Term (Fin d)} : 1 ≤ i → C d 0 h → C d i h

end LogicLineages.ComputabilityKnowledge.WWGroundClasses
