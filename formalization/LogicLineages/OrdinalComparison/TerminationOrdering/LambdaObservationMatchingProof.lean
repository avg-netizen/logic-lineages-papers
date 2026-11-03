module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment MarkedFAbsTest TypedObservationAccess LambdaObservationMatching

theorem originalBodyDecrease : LambdaObservationMatchingTargets.OriginalBodyDecrease := by
  intro Symbol inst arity I Γ σ υ body
  simp
  omega

theorem openingEnvironmentCalibration : LambdaObservationMatchingTargets.OpeningEnvironment := by
  intro Symbol inst arity I Γ P ρ σ υ i h
  exact ⟨rfl,fun {_} _ => rfl⟩

theorem genuineFreshOpening : LambdaObservationMatchingTargets.GenuineFreshOpening := by
  intro Symbol inst arity I P σ υ body ho
  obtain ⟨i,hi⟩ := MarkedFAbsTestProof.freshAvailability Symbol inst arity I P σ υ body ho
  obtain ⟨h,hbody⟩ := MarkedFAbsTestProof.genuineOpeningGuards Symbol inst arity I P σ υ body i ho hi
  exact ⟨i,h,hbody⟩

theorem literalMatch : LambdaObservationMatchingTargets.LiteralMatch := by
  intro Symbol inst arity I Γ σ υ body E P ρ strict targetBody
  simp only [matchTerm,decide_eq_true_eq]

theorem openingEnvironmentMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {P : World I} {ρ η : Environment I Γ P} (hρη : EnvLE ρ η)
    (σ υ : Ty) (i : Fin (budget I)) (h : Opening I P σ υ i) :
    EnvLE (openingEnvironment ρ σ υ i h) (openingEnvironment η σ υ i h) := by
  apply TypedValueEnvironmentProof.extensionMonotone Symbol inferInstance arity I Γ σ _ _ _ _ _ le_rfl
  exact TypedValueEnvironmentProof.restrictionMonotone Symbol inferInstance arity I Γ P _ _ ρ η hρη

theorem openedReadMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {body : MarkedTerm Symbol arity (σ::Γ) υ}
    {E F : BodyEvaluator I body} (hEF : EvaluatorsLE E F) {P : World I}
    {ρ η : Environment I Γ P} (hρη : EnvLE ρ η) (strict : Bool)
    (targetBody : Term Symbol arity (σ::(portTypes P.val++I.context)) υ)
    (i : Fin (budget I)) (h : Opening I P σ υ i) :
    openedRead strict E ρ targetBody i h ≤ openedRead strict F η targetBody i h := by
  apply TypedObservationAccessProof.readMonotone Symbol inferInstance arity I υ _ strict _ _ _
  exact hEF _ _ _ (openingEnvironmentMonotone hρη σ υ i h)

theorem matchMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {σ υ : Ty} {body : MarkedTerm Symbol arity (σ::Γ) υ}
    {E F : BodyEvaluator I body} (hEF : EvaluatorsLE E F) {P : World I}
    {ρ η : Environment I Γ P} (hρη : EnvLE ρ η) (strict : Bool)
    (t : Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ)) :
    matchTerm strict E ρ t ≤ matchTerm strict F η t := by
  cases t <;> try exact le_rfl
  case lam targetBody =>
    apply Bool.le_iff_imp.mpr
    simp only [matchTerm,decide_eq_true_eq]
    rintro ⟨i,h,hw⟩
    exact ⟨i,h,Bool.le_iff_imp.mp (openedReadMonotone hEF hρη strict targetBody i h) hw⟩

theorem bitsMonotone : LambdaObservationMatchingTargets.BitsMonotone := by
  intro Symbol inst arity I Γ σ υ body E F P ρ η hEF hρη Q
  have he : EnvLE (restrict Q.property ρ) (restrict Q.property η) :=
    TypedValueEnvironmentProof.restrictionMonotone Symbol inst arity I Γ P Q.val Q.property ρ η hρη
  exact ⟨le_rfl,fun o => matchMonotone hEF he false (observationBody o),fun o => matchMonotone hEF he true (observationBody o)⟩

theorem bitsRestriction : LambdaObservationMatchingTargets.BitsRestriction := by
  intro Symbol inst arity I Γ σ υ body E P Q h ρ
  funext R
  simp only [FiniteObservationBits.weaken,lambdaBits,
    TypedValueEnvironmentProof.restrictionComposition Symbol inst arity I Γ]

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaObservationMatchingProof
