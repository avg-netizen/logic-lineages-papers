module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FAbsStageSoundnessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessTargets
open Source FiniteObservationBits CoherentConstructorLattice ConstructorInputLogicalRelation SourceConstructorIteration

def OperatorPreservation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I),
  FamilySound I above M → FamilySound I above (SourceConstructorOperatorProof.operator above M)

def ActualIteratesSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (n : Nat),
  FamilySound I above (iterate I above n)

def ActualLimitSound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above),
  FamilySound I above (limit I above)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessTargets
