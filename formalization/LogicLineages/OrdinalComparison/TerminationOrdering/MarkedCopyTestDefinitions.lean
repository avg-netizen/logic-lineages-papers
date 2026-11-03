module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalNaturalityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTest
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess OrdinaryObservationView

instance headAboveDecision {Symbol : Type} (above : Symbol → Symbol → Prop) [DecidableRel above]
    (f g : Head Symbol) : Decidable (RecursiveComparison.headAbove above f g) := by
  cases f <;> cases g <;> unfold RecursiveComparison.headAbove <;> infer_instance

/-- Retype the same actual marked constructor state at the literal child result type. -/
def childWeak {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) : Bool :=
  if ht : o.resultType ∈ types I then readBit false (M.val f ⟨o.resultType,ht⟩ P a) o else false

def allChildrenWeak {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) : Bool := (plainChildren o).all (childWeak M f a)

def copyTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I)
    {P : World I} (a : Inputs I f P) (o : Observation Symbol arity I.context (budget I)) : Bool :=
  match rootView o.body with
  | none => false
  | some ⟨g,_⟩ => decide (RecursiveComparison.headAbove above f.val g) && allChildrenWeak M f a o

abbrev Coordinates {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (τ : Ty) (P : World I) :=
  (Q : Future P) → ObservationAt I τ Q.val → Bool

def copyCoordinates {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I) (τ : Ty)
    {P : World I} (a : Inputs I f P) : Coordinates I τ P :=
  fun Q o => copyTest above M f ((inputFamily I f).restrict Q.property a) o.val

def project {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P Q : World I}
    (h : Extends P Q) (c : Coordinates I τ P) : Coordinates I τ Q :=
  fun R o => c ⟨R.val,fun p hp => R.property p (h p hp)⟩ o

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedCopyTest
