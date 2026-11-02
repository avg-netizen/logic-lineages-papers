module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationTargets
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains CoherentConstructorLattice ExecutableDomainBottom SourceConstructorIteration

def BottomLeast : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (M : Constructors I), bottomConstructors I ≤ M

def AscendingIteration : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (n : Nat), iterate I above n ≤ iterate I above (n+1)

def CardinalityStabilization : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above), iterate I above (fuel I)=iterate I above (fuel I+1)

def ActualFixedPoint : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above), SourceConstructorOperatorProof.operator above (limit I above)=limit I above

def LeastPreFixedPoint : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (M : Constructors I), SourceConstructorOperatorProof.operator above M ≤ M → limit I above ≤ M

def EventualConstancy : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (n : Nat), fuel I ≤ n → iterate I above n=limit I above

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationTargets
