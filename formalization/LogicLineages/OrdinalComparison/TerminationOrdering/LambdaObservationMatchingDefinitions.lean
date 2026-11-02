module
public import LogicLineages.OrdinalComparison.TerminationOrdering.TypedValueEnvironmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatching
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment MarkedFAbsTest TypedObservationAccess

/-- A supplied evaluator for one fixed original body. This is not a definition of interpretation. -/
structure BodyEvaluator {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) {Γ : List Ty} {σ υ : Ty}
    (_body : MarkedTerm Symbol arity (σ::Γ) υ) where
  evaluate : (P : World I) → Environment I (σ::Γ) P → Value I υ P

def openingEnvironment {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {P : World I} (ρ : Environment I Γ P) (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i) :
    Environment I (σ::Γ) ⟨(i,σ)::P.val,h.2.1⟩ :=
  extend (LiteralVariableValueProof.variableValue (I := I) (P := ⟨(i,σ)::P.val,h.2.1⟩) Variable.here)
    (restrict (fun p hp => List.mem_cons_of_mem _ hp) ρ)

def openedRead {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {sourceBody : MarkedTerm Symbol arity (σ::Γ) υ}
    (strict : Bool) (E : BodyEvaluator I sourceBody) {P : World I} (ρ : Environment I Γ P)
    (targetBody : Term Symbol arity (σ::(portTypes P.val++I.context)) υ)
    (i : Fin (budget I)) (h : Opening I P σ υ i) : Bool :=
  readBit strict (E.evaluate _ (openingEnvironment ρ σ υ i h)) ⟨(i,σ)::P.val,υ,targetBody⟩

def matchTerm {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {sourceBody : MarkedTerm Symbol arity (σ::Γ) υ}
    (strict : Bool) (E : BodyEvaluator I sourceBody) {P : World I} (ρ : Environment I Γ P) :
    Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ) → Bool
  | .lam body => decide (∃ i : Fin (budget I),∃ h : Opening I P σ υ i,openedRead strict E ρ body i h=true)
  | _ => false

def observationBody {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity} {τ : Ty} {P : World I}
    (o : ObservationAt I τ P) : Term Symbol arity (portTypes P.val++I.context) τ :=
  Eq.mp (congrArg (Term Symbol arity (portTypes P.val++I.context)) o.property.2.2)
    (bodyAtWorld P o.val o.property.2.1)

def lambdaBits {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {sourceBody : MarkedTerm Symbol arity (σ::Γ) υ}
    (E : BodyEvaluator I sourceBody) {P : World I} (ρ : Environment I Γ P) : Bits I (.arrow σ υ) P :=
  fun Q => (true,fun o => matchTerm false E (restrict Q.property ρ) (observationBody o),
    fun o => matchTerm true E (restrict Q.property ρ) (observationBody o))

def EvaluatorsLE {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {sourceBody : MarkedTerm Symbol arity (σ::Γ) υ}
    (E F : BodyEvaluator I sourceBody) : Prop :=
  ∀ P (ρ η : Environment I (σ::Γ) P),EnvLE ρ η → E.evaluate P ρ ≤ F.evaluate P η

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatching
