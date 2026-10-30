module

public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

@[expose] public section

/-! Original closed assignment domain, Wilken–Weiermann Definitions 2.5–2.6.
The B classes use the literal six simultaneous rules, not a numerical domain
replacement. The finite extraction in the collapse side condition is totalized;
its agreement with the original finite g is a proof obligation from B0.
Lists representing source vectors are nonempty; getD zero implements the
source convention that all components beyond the level are zero. -/
namespace LogicLineages.ComputabilityKnowledge.WWClosedAssignment

open WWOrdinalTermSemantics
open LogicLineages.OrdinalComparison

noncomputable def closedValue (t : Term Empty) : Ordinal.{0} := denote Empty.elim t

inductive B : Nat → Term Empty → Prop where
  | one (i : Nat) : B i .one
  | omega (i : Nat) (hi : 1 ≤ i) : B i .omega
  | add {i : Nat} {f g : Term Empty} : B i f → B i g → B i (.add f g)
  | emul {i : Nat} {f g : Term Empty} : 1 ≤ i → B (i + 1) f → B i g → B i (.emul f g)
  | collapse {f g : Term Empty} : B 1 f → B 0 g →
      actualOrdinalNorm (closedValue f) ≤ fastControl 2 (closedValue g).card.toNat →
      B 0 (.collapse f g)
  | lift {i : Nat} {h : Term Empty} : 1 ≤ i → B 0 h → B i h

def positiveNumeral : Nat → Term Empty
  | 0 => .one
  | n + 1 => .add (positiveNumeral n) .one

noncomputable def BoundedNorm (xs : List (Term Empty)) : Prop :=
  ∀ i : Nat, actualOrdinalNorm (closedValue (xs.getD i .zero)) ≤
    actualOrdinalNorm (closedValue (xs.getD 0 .zero))

end LogicLineages.ComputabilityKnowledge.WWClosedAssignment
