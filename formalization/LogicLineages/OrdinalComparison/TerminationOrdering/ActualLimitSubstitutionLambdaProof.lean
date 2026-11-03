module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionLambdaProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport LambdaSpineActions LambdaObservationMatching ActualLimitSubstitutionSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem openingAgreement {Γ Δ : List Ty} (M : Constructors I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    {P : World I} (ρ : Environment I Γ P) (η : Environment I Δ P) (ha : Agreement M s hs ρ η)
    (σ υ : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P σ υ i) :
    Agreement M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs)
      (openingEnvironment ρ σ υ i h) (openingEnvironment η σ υ i h) := by
  exact SubstitutionEnvironmentSupportProof.agreementLift Symbol inferInstance arity I Γ Δ σ M s hs _ _ _ _
    (SubstitutionEnvironmentSupportProof.agreementRestriction Symbol inferInstance arity I Γ Δ M s hs P _ _ ρ η ha)

theorem consumeEq {Γ Δ : List Ty} {σ υ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (A : PairedAction I (σ::Γ) υ) (B : PairedAction I (σ::Δ) υ)
    (hab : Related M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) A B)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (ha : Agreement M s hs ρ η)
    (sm : Protected Γ) (tm : Protected Δ) (hc : ProtectedCompatible I s sm tm)
    (α : Ty) (rest : List Ty) (τ : Ty) (args : Values I (α::rest) P) (h : Ty.arrow σ υ=arrows (α::rest) τ) :
    consume B M P η tm α rest τ args h=consume A M P ρ sm α rest τ args h := by
  exact (hab P _ _ (SubstitutionEnvironmentSupportProof.agreementLift Symbol inferInstance arity I Γ Δ σ M s hs P _ ρ η ha)).2
    _ _ (ConfinedSubstitutionProof.liftedCompatibility Symbol inferInstance arity I Γ Δ σ s sm tm hc)
    rest τ (tailValues args) (Ty.arrow.inj h).2

theorem nonemptyEq {Γ Δ : List Ty} {σ υ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (A : PairedAction I (σ::Γ) υ) (B : PairedAction I (σ::Δ) υ)
    (hab : Related M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) A B)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (ha : Agreement M s hs ρ η)
    (sm : Protected Γ) (tm : Protected Δ) (hc : ProtectedCompatible I s sm tm)
    (types : List Ty) (τ : Ty) (args : Values I types P) (h : Ty.arrow σ υ=arrows types τ) (hn : types≠[]) :
    consumeNonempty B M P η tm types τ args h hn=consumeNonempty A M P ρ sm types τ args h hn := by
  cases types with
  | nil => exact False.elim (hn rfl)
  | cons α rest => exact consumeEq M s hs A B hab P ρ η ha sm tm hc α rest τ args h

theorem matchEq {Γ Δ : List Ty} {σ υ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (B : PairedAction I (σ::Δ) υ)
    (hab : Related M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) A B)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (ha : Agreement M s hs ρ η)
    (strict : Bool) (t : Term Symbol arity (portTypes P.val++I.context) (.arrow σ υ)) :
    matchTerm strict (bodyEvaluator (substituteTerm body (liftSubstitution s)) B M) η t=
      matchTerm strict (bodyEvaluator body A M) ρ t := by
  cases t <;> try rfl
  case lam targetBody =>
    simp only [matchTerm,openedRead,bodyEvaluator]
    congr 1
    apply propext
    constructor <;> rintro ⟨i,h,hw⟩
    · refine ⟨i,h,?_⟩
      have he := (hab _ _ _ (openingAgreement M s hs ρ η ha σ υ i h)).1
      rw [he] at hw
      exact hw
    · refine ⟨i,h,?_⟩
      have he := (hab _ _ _ (openingAgreement M s hs ρ η ha σ υ i h)).1
      rw [he]
      exact hw

theorem rawEq {Γ Δ : List Ty} {σ υ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (B : PairedAction I (σ::Δ) υ)
    (hab : Related M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) A B)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (ha : Agreement M s hs ρ η) :
    lambdaRaw (substituteTerm body (liftSubstitution s)) B M P η=lambdaRaw body A M P ρ := by
  apply Prod.ext
  · funext Q
    have hq : Agreement M s hs (restrict Q.property ρ) (restrict Q.property η) := SubstitutionEnvironmentSupportProof.agreementRestriction Symbol inferInstance arity I Γ Δ M s hs P Q.val Q.property ρ η ha
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext o
        exact matchEq M s hs body A B hab Q.val _ _ hq false (observationBody o)
      · funext o
        exact matchEq M s hs body A B hab Q.val _ _ hq true (observationBody o)
  · funext Q suffix args
    exact nonemptyEq M s hs A B hab Q.val _ _
      (SubstitutionEnvironmentSupportProof.agreementRestriction Symbol inferInstance arity I Γ Δ M s hs P Q.val Q.property ρ η ha)
      _ _ (ConfinedSubstitutionProof.initiallyCompatible Symbol inferInstance arity I Γ Δ s)
      suffix.val.1 suffix.val.2 args _ _

theorem lambdaRelated {Γ Δ : List Ty} {σ υ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) (B : PairedAction I (σ::Δ) υ)
    (hab : Related M (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I Γ Δ σ s hs) A B) :
    Related M s hs (LambdaSpineActionsProof.lambdaAction body A)
      (LambdaSpineActionsProof.lambdaAction (substituteTerm body (liftSubstitution s)) B) := by
  intro P ρ η ha
  have he : LambdaSpineActionsProof.lambdaValue (substituteTerm body (liftSubstitution s)) B M P η=
      LambdaSpineActionsProof.lambdaValue body A M P ρ := by
    apply RecursiveNaturalDomainsProof.layerViewInjective I (.arrow σ υ) P
    apply Subtype.ext
    exact (LambdaSpineActionsProof.valueLayer _ B M P η).trans
      ((rawEq M s hs body A B hab P ρ η ha).trans (LambdaSpineActionsProof.valueLayer body A M P ρ).symm)
  refine ⟨he,?_⟩
  intro sm tm hc types τ args h
  change lambdaScan B _ M P η tm types τ args h=lambdaScan A _ M P ρ sm types τ args h
  by_cases hn : types=[]
  · simp only [lambdaScan,dif_pos hn]
    exact congrArg (castValue _) he
  · simp only [lambdaScan,dif_neg hn]
    exact nonemptyEq M s hs A B hab P ρ η ha sm tm hc types τ args h hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionLambdaProof
