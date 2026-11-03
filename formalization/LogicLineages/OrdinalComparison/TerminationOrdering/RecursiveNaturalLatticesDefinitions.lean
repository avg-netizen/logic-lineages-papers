module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NaturalLayerBoundsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLattices
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains

/-- Completeness of the pre-existing computed carrier in its unchanged actual order. -/
def CompleteAt {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (τ : Ty) (P : World I) : Prop :=
  ∃ C : CompleteLattice (Value I τ P),C.toPartialOrder=(family I τ).order P

def SupPreserving {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {τ : Ty} {P Q : World I} (h : Extends P Q) : Prop :=
  ∀ (S : Set (Value I τ P)) (a : Value I τ P),IsLUB S a →
    IsLUB (RecursiveNaturalDomains.weaken h '' S) (RecursiveNaturalDomains.weaken h a)

def InfPreserving {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    {I : Input Symbol arity} {τ : Ty} {P Q : World I} (h : Extends P Q) : Prop :=
  ∀ (S : Set (Value I τ P)) (a : Value I τ P),IsGLB S a →
    IsGLB (RecursiveNaturalDomains.weaken h '' S) (RecursiveNaturalDomains.weaken h a)

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveNaturalLattices
