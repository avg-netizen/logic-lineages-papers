module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue FunctionalSpineActions FunctionalSpineActionsSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

 theorem stateMonotone : FunctionalSpineActionsTargets.StateMonotone := FunctionalSpineActionsSupportProof.stateMonotone
 theorem stateRestriction : FunctionalSpineActionsTargets.StateRestriction := FunctionalSpineActionsSupportProof.stateRestriction
 theorem fullTupleScanEquation : FunctionalSpineActionsTargets.FullTupleScanEquation := FunctionalSpineActionsSupportProof.fullTupleScanEquation
 theorem evaluationEquations : FunctionalSpineActionsTargets.EvaluationEquations := FunctionalSpineActionsSupportProof.evaluationEquations

theorem scanMonotone {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (e : Evaluate I Γ σ.val)
    (state : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P)
    (he : EvaluationMonotone e)
    (hs : ∀ M N P (ρ η : Environment I Γ P),M ≤ N → EnvLE ρ η → state M P ρ ≤ state N P η) :
    ScanMonotone (functionalScan f σ e state) := by
  intro M N P ρ η mask types τ args args' h hMN hρη ha
  by_cases hn : types=[]
  · subst types
    cases h
    simp only [functionalScan,dif_pos rfl]
    exact he M N P ρ η hMN hρη
  · simp only [functionalScan,dif_neg hn]
    apply le_trans (hMN f _ P _)
    apply N.property.1
    exact FunctionalTupleBuilderProof.appendInputMonotone (hs M N P ρ η hMN hρη)
      (FullTuplePackingProof.pointwiseDomination Symbol inferInstance arity I σ (sourceSuffix σ types τ h hn) P args args' ha)

theorem scanNatural {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (e : Evaluate I Γ σ.val)
    (state : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P)
    (he : EvaluationNatural e)
    (hs : ∀ M P Q (h : Extends P Q) (ρ : Environment I Γ P),(inputFamily I f).restrict h (state M P ρ)=state M Q (restrict h ρ)) :
    ScanNatural (functionalScan f σ e state) := by
  intro M P Q hPQ ρ mask types τ args h
  by_cases hn : types=[]
  · subst types
    cases h
    simp only [functionalScan,dif_pos rfl]
    exact he M P Q hPQ ρ
  · simp only [functionalScan,dif_neg hn]
    let s : Suffix σ.val := sourceSuffix σ types τ h hn
    let av : FullTuple I σ.val s P := args
    exact (M.property.2 f (resultTag I σ s) P Q hPQ
      (FunctionalTupleBuilder.appendInput (state M P ρ) (packTuple σ s av))).trans
      (congrArg (M.val f (resultTag I σ s) Q)
        ((FunctionalTupleBuilderProof.appendInputRestriction hPQ (state M P ρ) (packTuple σ s av)).trans
          (congrArg₂ FunctionalTupleBuilder.appendInput (hs M P Q hPQ ρ)
            (FullTuplePackingProof.weakeningMap Symbol inferInstance arity I σ s P Q hPQ av))))

def assembleAction {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (e : Evaluate I Γ σ.val)
    (state : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P)
    (hem : EvaluationMonotone e) (hen : EvaluationNatural e)
    (hsm : ∀ M N P (ρ η : Environment I Γ P),M ≤ N → EnvLE ρ η → state M P ρ ≤ state N P η)
    (hsn : ∀ M P Q (h : Extends P Q) (ρ : Environment I Γ P),(inputFamily I f).restrict h (state M P ρ)=state M Q (restrict h ρ)) :
    PairedAction I Γ σ.val where
  evaluate := e
  scan := functionalScan f σ e state
  evaluateMonotone := hem
  evaluateNatural := hen
  scanMonotone := scanMonotone f σ e state hem hsm
  scanNatural := scanNatural f σ e state hen hsn
  scanEmpty := by
    intro M P ρ mask args
    simp only [functionalScan,dif_pos rfl]
    rfl

theorem ordinaryMonotone {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) :
    EvaluationMonotone (ordinaryEvaluate f base) := by
  intro M N P ρ η hMN hρη
  exact OrdinaryFunctionalNaturalityProof.valueMonotone Symbol inferInstance arity I f M N P _ _ hMN
    (argumentsMonotone base hMN hρη)

theorem ordinaryNatural {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) :
    EvaluationNatural (ordinaryEvaluate f base) := by
  intro M P Q h ρ
  change RecursiveNaturalDomains.weaken h (ordinaryValue M f (evaluateArguments base M P ρ)) = _
  rw [OrdinaryFunctionalNaturalityProof.valueWeakening]
  change ordinaryValue M f (weakenValues h (evaluateArguments base M P ρ)) = _
  rw [argumentsRestriction]
  rfl

def ordinaryAction {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val)) :
    PairedAction I Γ (headResult f.val) :=
  assembleAction f ⟨headResult f.val,OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inferInstance arity I f⟩
    (ordinaryEvaluate f base) (ordinaryState f base) (ordinaryMonotone f base) (ordinaryNatural f base)
    (fun _ _ _ _ _ hMN hρη => ordinaryStateMonotone f base hMN hρη)
    (fun M _ _ h ρ => ordinaryStateRestriction f base M h ρ)

theorem markedMonotone {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) :
    EvaluationMonotone (markedEvaluate f σ base extraTypes ht extras) := by
  intro M N P ρ η hMN hρη
  exact le_trans (hMN f σ P _) (N.property.1 f σ P _ _
    (stateMonotone Symbol inferInstance arity I Γ f base extraTypes ht extras M N P ρ η hMN hρη))

theorem markedNatural {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) :
    EvaluationNatural (markedEvaluate f σ base extraTypes ht extras) := by
  intro M P Q h ρ
  change RecursiveNaturalDomains.weaken h (M.val f σ P (markedState f base extraTypes ht extras M P ρ)) = _
  rw [M.property.2,stateRestriction]
  rfl

def markedAction {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes) :
    PairedAction I Γ σ.val :=
  assembleAction f σ (markedEvaluate f σ base extraTypes ht extras) (markedState f base extraTypes ht extras)
    (markedMonotone f σ base extraTypes ht extras) (markedNatural f σ base extraTypes ht extras)
    (stateMonotone Symbol inferInstance arity I Γ f base extraTypes ht extras)
    (stateRestriction Symbol inferInstance arity I Γ f base extraTypes ht extras)

theorem actualOrdinaryAction : FunctionalSpineActionsTargets.ActualOrdinaryAction := by
  intro Symbol inst arity I Γ f base
  exact ⟨ordinaryAction f base,rfl,rfl⟩

theorem actualMarkedAction : FunctionalSpineActionsTargets.ActualMarkedAction := by
  intro Symbol inst arity I Γ f σ base extraTypes ht extras
  exact ⟨markedAction f σ base extraTypes ht extras,rfl,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsProof
