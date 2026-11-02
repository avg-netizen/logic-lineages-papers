module
public import LogicLineages.OrdinalComparison.TerminationOrdering.MarkedSelectTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTest
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice TypedObservationAccess MarkedCopyTest

def Opening {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I) (σ υ : Ty) (i : Fin (budget I)) : Prop :=
  i ∉ P.val.map Prod.fst ∧ ((i,σ)::P.val) ∈ worldList I ∧ σ ∈ types I ∧ υ ∈ types I
instance openingDecision {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) (P : World I) (σ υ : Ty) (i : Fin (budget I)) : Decidable (Opening I P σ υ i) :=
  inferInstanceAs (Decidable (i ∉ P.val.map Prod.fst ∧ ((i,σ)::P.val) ∈ worldList I ∧ σ ∈ types I ∧ υ ∈ types I))

def openingInput {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (f : HeadIndex I) {P : World I} (a : Inputs I f P) (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i) :
    Inputs I f ⟨(i,σ)::P.val,h.2.1⟩ :=
  let ext : Extends P ⟨(i,σ)::P.val,h.2.1⟩ := fun p hp => List.mem_cons_of_mem _ hp
  FunctionalTupleBuilder.appendInput ((inputFamily I f).restrict ext a)
    [⟨⟨σ,h.2.2.1⟩,LiteralVariableValueProof.variableValue (I := I) (P := ⟨(i,σ)::P.val,h.2.1⟩) Variable.here⟩]

def openingRead {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P) (σ υ : Ty)
    (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) (i : Fin (budget I)) (h : Opening I P σ υ i) : Bool :=
  readBit false (M.val f ⟨υ,h.2.2.2⟩ ⟨(i,σ)::P.val,h.2.1⟩ (openingInput f a σ υ i h)) ⟨(i,σ)::P.val,υ,body⟩

def lambdaTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P) (σ υ : Ty)
    (body : Term Symbol arity (σ::(portTypes P.val++I.context)) υ) : Bool :=
  decide (∃ i : Fin (budget I),∃ h : Opening I P σ υ i,openingRead M f a σ υ body i h=true)

/-- Only context transport, preserving the literal original body and all syntax. -/
def bodyAtWorld {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} (P : World I)
    (o : Observation Symbol arity I.context (budget I)) (h : o.ports=P.val) : Term Symbol arity (portTypes P.val++I.context) o.resultType :=
  Eq.mp (congrArg (fun ports => Term Symbol arity (portTypes ports++I.context) o.resultType) h) o.body

def termTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P) :
    {τ : Ty} → Term Symbol arity (portTypes P.val++I.context) τ → Bool
  | _, .lam (σ := σ) (τ := υ) body => lambdaTest M f a σ υ body
  | _, _ => false

def fAbsTest {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (a : Inputs I f P)
    (o : Observation Symbol arity I.context (budget I)) : Bool :=
  if hp : o.ports=P.val then termTest M f a (bodyAtWorld P o hp) else false

def fAbsCoordinates {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) (τ : Ty) {P : World I} (a : Inputs I f P) : Coordinates I τ P :=
  fun Q o => fAbsTest M f ((inputFamily I f).restrict Q.property a) o.val

end LogicLineages.OrdinalComparison.TerminationOrdering.MarkedFAbsTest
