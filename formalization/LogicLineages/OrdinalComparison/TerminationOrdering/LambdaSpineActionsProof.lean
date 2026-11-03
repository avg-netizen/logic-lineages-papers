module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions LambdaObservationMatching LambdaSpineActions LambdaSpineActionsSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem binderProtection : LambdaSpineActionsTargets.BinderProtection := LambdaSpineActionsSupportProof.binderProtection
theorem binderConsumption : LambdaSpineActionsTargets.BinderConsumption := LambdaSpineActionsSupportProof.binderConsumption

theorem naturalTables : LambdaSpineActionsTargets.NaturalTables := by
  intro Symbol inst arity I Γ σ υ body A M P ρ
  constructor
  · intro Q s args args' ha
    exact nonemptyMonotone A le_rfl (fun {_} _ => le_rfl) _ _ _ args args' _ _ ha
  · intro Q R h s args
    have hn := (Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration (.arrow σ υ) s.val.1 s.val.2).mp s.property
    have hw := nonemptyNatural A M h (restrict Q.property ρ) (fun {_} _ => false) s.val.1 s.val.2 args hn.2.symm hn.1
    change RecursiveNaturalDomains.weaken h
      (consumeNonempty A M Q.val (restrict Q.property ρ) (fun {_} _ => false) s.val.1 s.val.2 args hn.2.symm hn.1) =
      consumeNonempty A M R.val (restrict R.property ρ) (fun {_} _ => false) s.val.1 s.val.2 (weakenValues h args) hn.2.symm hn.1
    have he : @Eq (Environment I Γ R.val) (restrict h (restrict Q.property ρ)) (restrict R.property ρ) :=
      TypedValueEnvironmentProof.restrictionComposition Symbol inst arity I Γ P Q.val R.val Q.property h ρ
    exact hw.trans (congrArg (fun env : Environment I Γ R.val =>
      consumeNonempty A M R.val env (fun {_} _ => false) s.val.1 s.val.2 (weakenValues h args) hn.2.symm hn.1) he)

theorem rawMonotone : LambdaSpineActionsTargets.RawMonotone := by
  intro Symbol inst arity I Γ σ υ body A M N P ρ η hMN hρη
  constructor
  · exact LambdaObservationMatchingProof.bitsMonotone Symbol inst arity I Γ σ υ body
      (bodyEvaluator body A M) (bodyEvaluator body A N) P ρ η
      (fun Q a b hab => A.evaluateMonotone M N Q a b hMN hab) hρη
  · intro Q s args
    exact nonemptyMonotone A hMN
      (TypedValueEnvironmentProof.restrictionMonotone Symbol inst arity I Γ P Q.val Q.property ρ η hρη)
      _ _ _ args args _ _ le_rfl

theorem rawRestriction : LambdaSpineActionsTargets.RawRestriction := by
  intro Symbol inst arity I Γ σ υ body A M P Q h ρ
  apply Prod.ext
  · exact LambdaObservationMatchingProof.bitsRestriction Symbol inst arity I Γ σ υ body (bodyEvaluator body A M) P Q h ρ
  · funext R s args
    simp only [rawWeaken,lambdaRaw,TypedValueEnvironmentProof.restrictionComposition Symbol inst arity I Γ]

def lambdaValue {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) :
    Evaluate I Γ (.arrow σ υ) := fun M P ρ =>
  layerFold I (.arrow σ υ) P ⟨lambdaRaw body A M P ρ,naturalTables Symbol inferInstance arity I Γ σ υ body A M P ρ⟩

theorem valueLayer {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    (layerView I (.arrow σ υ) P (lambdaValue body A M P ρ)).val=lambdaRaw body A M P ρ := by
  simp only [lambdaValue,RecursiveNaturalDomainsProof.layerViewFold]

theorem valueMonotone {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) :
    EvaluationMonotone (lambdaValue body A) := by
  intro M N P ρ η hMN hρη
  apply (RecursiveNaturalDomainsProof.transportOrder (family I (.arrow σ υ))
    (NaturalTupleLayerProof.layerFamily I (.arrow σ υ) (lower I (.arrow σ υ))) (familyEquation I (.arrow σ υ)) P _ _).mpr
  change layerView I (.arrow σ υ) P (lambdaValue body A M P ρ) ≤ layerView I (.arrow σ υ) P (lambdaValue body A N P η)
  change (layerView I (.arrow σ υ) P (lambdaValue body A M P ρ)).val ≤ (layerView I (.arrow σ υ) P (lambdaValue body A N P η)).val
  rw [valueLayer,valueLayer]
  exact rawMonotone Symbol inferInstance arity I Γ σ υ body A M N P ρ η hMN hρη

theorem valueNatural {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) :
    EvaluationNatural (lambdaValue body A) := by
  intro M P Q h ρ
  apply RecursiveNaturalDomainsProof.layerViewInjective I (.arrow σ υ) Q
  rw [RecursiveNaturalDomainsProof.layerViewWeaken]
  apply Subtype.ext
  change rawWeaken h (layerView I (.arrow σ υ) P (lambdaValue body A M P ρ)).val = (layerView I (.arrow σ υ) Q (lambdaValue body A M Q (restrict h ρ))).val
  rw [valueLayer,valueLayer]
  exact rawRestriction Symbol inferInstance arity I Γ σ υ body A M P Q h ρ

theorem scanMonotone {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ) (e : Evaluate I Γ (.arrow σ υ))
    (he : EvaluationMonotone e) : ScanMonotone (lambdaScan A e) := by
  intro M N P ρ η mask types τ args args' h hMN hρη ha
  by_cases hn : types=[]
  · simp only [lambdaScan,dif_pos hn]
    exact castMonotone _ (he M N P ρ η hMN hρη)
  · simp only [lambdaScan,dif_neg hn]
    exact nonemptyMonotone A hMN hρη mask types τ args args' h hn ha

theorem scanNatural {Γ : List Ty} {σ υ : Ty} (A : PairedAction I (σ::Γ) υ) (e : Evaluate I Γ (.arrow σ υ))
    (he : EvaluationNatural e) : ScanNatural (lambdaScan A e) := by
  intro M P Q hPQ ρ mask types τ args h
  by_cases hn : types=[]
  · simp only [lambdaScan,dif_pos hn]
    exact (castNatural hPQ _ (e M P ρ)).trans (congrArg (castValue _) (he M P Q hPQ ρ))
  · simp only [lambdaScan,dif_neg hn]
    exact nonemptyNatural A M hPQ ρ mask types τ args h hn

def lambdaAction {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ) (A : PairedAction I (σ::Γ) υ) :
    PairedAction I Γ (.arrow σ υ) where
  evaluate := lambdaValue body A
  scan := lambdaScan A (lambdaValue body A)
  evaluateMonotone := valueMonotone body A
  evaluateNatural := valueNatural body A
  scanMonotone := scanMonotone A (lambdaValue body A) (valueMonotone body A)
  scanNatural := scanNatural A (lambdaValue body A) (valueNatural body A)
  scanEmpty := by
    intro M P ρ mask args
    simp only [lambdaScan,dif_pos rfl]
    rfl

theorem actualLambdaAction : LambdaSpineActionsTargets.ActualLambdaAction := by
  intro Symbol inst arity I Γ σ υ body A
  exact ⟨lambdaAction body A,fun M P ρ => valueLayer body A M P ρ,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.LambdaSpineActionsProof
