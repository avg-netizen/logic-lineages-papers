module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalTupleBuilderProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottom
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

/-- A discharged Prop witness only; it is erased from finite-search execution. -/
theorem leastWitness {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) :
    ∃! a : Value I τ P,a ∈ enumerateValues I τ P ∧ ∀ b,a ≤ b := by
  obtain ⟨a,ha⟩ := RecursiveNaturalLatticesProof.supremumExistence Symbol inferInstance arity I τ P ∅
  have hleast : ∀ b,a ≤ b := fun b => ha.2 (by intro x hx; cases hx)
  refine ⟨a,⟨RecursiveNaturalDomainsProof.exhaustiveEnumeration Symbol inferInstance arity I τ P a,hleast⟩,?_⟩
  intro b hb
  exact le_antisymm (hb.2 a) (hleast b)

/-- Ordinary decidable finite search on the actual enumerated domain/order. -/
def bottomValue {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Value I τ P :=
  (enumerateValues I τ P).choose (fun a => ∀ b,a ≤ b) (leastWitness I τ P)

end LogicLineages.OrdinalComparison.TerminationOrdering.ExecutableDomainBottom
