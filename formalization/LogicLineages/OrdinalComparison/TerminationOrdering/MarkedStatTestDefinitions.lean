module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTest
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView OrdinaryFunctionalValue FiniteOccurrenceMatching MarkedCopyTest

/-- Stat compares only the full fixed base tuple; extras occur solely in the same-source child calls. -/
def statTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) : Bool :=
  match rootView o.body with
  | none => false
  | some ⟨g,_⟩ => decide (RecursiveComparison.headEquivalent f.val g) &&
      strictTest (pairBit false) (pairBit true) (packBase f a.1) (plainChildren o) && allChildrenWeak M f a o

def statCoordinates {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (τ : Ty) {P : World I} (a : Inputs I f P) : Coordinates I τ P :=
  fun Q o => statTest M f ((inputFamily I f).restrict Q.property a) o.val

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedStatTest
