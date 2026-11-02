module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkLambdaProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation RecursiveComparison TypedObservationAccess SourceConstructorIteration ActualStrictMark FunctionalSpineActions OriginalSpineActions LambdaObservationMatching LambdaSpineActions ActualStrictMarkSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem matchingEq {Γ : List Ty} {σ υ : Ty} (body marked : MarkedTerm Symbol arity (σ::Γ) υ)
    (A B : PairedAction I (σ::Γ) υ) (M : Constructors I)
    (he : ∀ P (ρ : Environment I (σ::Γ) P) o,readBit true (A.evaluate M P ρ) o=readBit false (B.evaluate M P ρ) o)
    (P : World I) (ρ : Environment I Γ P) (t : Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ)) :
    matchTerm true (bodyEvaluator body A M) ρ t=matchTerm false (bodyEvaluator marked B M) ρ t := by
  cases t <;> try rfl
  case lam targetBody =>
    simp only [matchTerm,openedRead,bodyEvaluator]
    congr 1
    apply propext
    constructor <;> rintro ⟨i,h,hw⟩
    · exact ⟨i,h,(he _ _ _).symm.trans hw⟩
    · exact ⟨i,h,(he _ _ _).trans hw⟩

theorem lambdaReads {Γ : List Ty} {σ υ : Ty} (body marked : MarkedTerm Symbol arity (σ::Γ) υ)
    (A B : PairedAction I (σ::Γ) υ) (M : Constructors I)
    (he : ∀ P (ρ : Environment I (σ::Γ) P) o,readBit true (A.evaluate M P ρ) o=readBit false (B.evaluate M P ρ) o)
    (P : World I) (ρ : Environment I Γ P) (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)) :
    readBit true (LambdaSpineActionsProof.lambdaValue body A M P ρ) o=
      readBit false (LambdaSpineActionsProof.lambdaValue marked B M P ρ) o := by
  apply readsEqual
  intro Q obs
  simp only [coordinate,if_true,if_false,LambdaSpineActionsProof.valueLayer]
  exact matchingEq body marked A B M he Q.val (restrict Q.property ρ) (observationBody obs)

theorem matchingFalse {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ)
    (A : PairedAction I (σ::Γ) υ) (M : Constructors I)
    (he : ∀ P (ρ : Environment I (σ::Γ) P),VariablesStrictEmpty ρ → ∀ o,readBit true (A.evaluate M P ρ) o=false)
    (P : World I) (ρ : Environment I Γ P) (hρ : VariablesStrictEmpty ρ)
    (t : Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ)) :
    matchTerm true (bodyEvaluator body A M) ρ t=false := by
  cases t <;> try rfl
  case lam targetBody =>
    simp only [matchTerm,decide_eq_false_iff_not]
    rintro ⟨i,h,hw⟩
    have hf := he _ _ (openingEmpty ρ hρ σ υ i h) ⟨(i,σ)::P.val,υ,targetBody⟩
    exact Bool.false_ne_true (hf.symm.trans hw)

theorem lambdaEmpty {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ)
    (A : PairedAction I (σ::Γ) υ) (M : Constructors I)
    (he : ∀ P (ρ : Environment I (σ::Γ) P),VariablesStrictEmpty ρ → ∀ o,readBit true (A.evaluate M P ρ) o=false)
    (P : World I) (ρ : Environment I Γ P) (hρ : VariablesStrictEmpty ρ) :
    StrictEmpty (LambdaSpineActionsProof.lambdaValue body A M P ρ) := by
  intro Q o
  simp only [coordinate,if_true,LambdaSpineActionsProof.valueLayer]
  exact matchingFalse body A M he Q.val (restrict Q.property ρ)
    (fun {_} v => emptyWeaken Q.property (ρ v) (hρ v)) (observationBody o)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkLambdaProof
