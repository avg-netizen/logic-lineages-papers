module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTest
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryFunctionalValue FullTuplePacking MarkedCopyTest

def Selected {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} (a : Inputs I f P) (p : Packed I P) : Prop :=
  p ∈ packBase f a.1 ∨ contains a.2 p
instance selectedDecision {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} (a : Inputs I f P) (p : Packed I P) : Decidable (Selected f a p) :=
  inferInstanceAs (Decidable (p ∈ packBase f a.1 ∨ p.2 ∈ (a.2 p.1).val))

/-- Entire tuple of the same marked state, retyped separately at every argument type. -/
def selfTuple {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (τ : TypeIndex I) (s : Suffix τ.val) : FullTuple I τ.val s P :=
  fun i => M.val f (argumentTag I τ s i) P a

/-- Zero arguments are separate; nonempty suffixes use exactly one complete tuple application. -/
def candidateTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (p : Packed I P) (o : Observation Symbol arity I.context (budget I)) : Bool :=
  (decide (p.1.val=o.resultType) && readBit false p.2 o) ||
    decide (∃ s : Suffix p.1.val,s.val.2=o.resultType ∧ readBit false (applyValue p.2 s (selfTuple M f a p.1 s)) o=true)

/-- Executable finite quantification over the actual packed universe, with the literal selected guard. -/
def selectTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) : Bool :=
  decide (∃ p : Packed I P,Selected f a p ∧ candidateTest M f a p o=true)

def selectCoordinates {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (τ : Ty) {P : World I} (a : Inputs I f P) : Coordinates I τ P :=
  fun Q o => selectTest M f ((inputFamily I f).restrict Q.property a) o.val

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTest
