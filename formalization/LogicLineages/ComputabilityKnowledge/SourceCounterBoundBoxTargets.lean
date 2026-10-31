module
public import LogicLineages.ComputabilityKnowledge.SourceCounterBoundBoxDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox.Targets
def BoxMembership : Prop := ∀ r m xs, xs ∈ box r m ↔
  xs.length = m ∧ ∀ x ∈ xs, x+1 ≤ r
def BoxComputable : Prop := Computable₂ box
def RadiusComputable : Prop := ∀ {Q : Type*} [Primcodable Q]
  (arity : Q → Nat) (point : Q → List Nat → Bool),
  Computable arity → Computable₂ point → Computable₂ (radiusBad arity point)
def RadiusCorrect : Prop := ∀ {Q : Type*} (arity : Q → Nat)
  (point : Q → List Nat → Bool) q r,
  radiusBad arity point q r = true ↔
    ∃ xs, xs.length = arity q ∧ (∀ x ∈ xs, x+1 ≤ r) ∧ point q xs = false
def Exhaustive : Prop := ∀ {Q : Type*} (arity : Q → Nat)
  (point : Q → List Nat → Bool) q,
  (∀ r, radiusBad arity point q r = false) ↔
    ∀ xs, xs.length = arity q → point q xs = true
end LogicLineages.ComputabilityKnowledge.SourceCounterBoundBox.Targets
