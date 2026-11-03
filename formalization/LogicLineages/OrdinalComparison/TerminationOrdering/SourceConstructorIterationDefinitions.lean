module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorOperatorProof
public import Mathlib.Data.Fintype.Card

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIteration
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains CoherentConstructorLattice ExecutableDomainBottom

/-- Pointwise actual bottom; its certificate reuses independently proved actual bottom laws. -/
def bottomConstructors {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Constructors I :=
  ⟨fun _ τ P _ => bottomValue I τ.val P,by
    constructor
    · intro f τ P a b hab; exact le_rfl
    · intro f τ P Q h a
      exact ExecutableDomainBottomProof.weakeningBottom Symbol inferInstance arity I τ.val P Q h⟩

/-- Source-specific recursion: only the actual proved source F is iterated. -/
def iterate {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) [DecidableRel above] : Nat → Constructors I
  | 0 => bottomConstructors I
  | n+1 => SourceConstructorOperatorProof.operator above (iterate I above n)

def fuel {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity) : Nat :=
  Fintype.card (Constructors I)

def limit {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) [DecidableRel above] : Constructors I := iterate I above (fuel I)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIteration
