module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue ConfinedStructuralInterpretation SourceConstructorIteration ActualLimitApplicationSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem markedApplication (above : Symbol → Symbol → Prop) [DecidableRel above]
    {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes)
    (P : World I) (ρ : Environment I Γ P) (types : List Ty) (τ : Ty) (args : Values I types P)
    (h : σ.val=arrows types τ) (hn : types≠[]) :
    applyWith ((FunctionalSpineActionsProof.markedAction f σ base extraTypes ht extras).evaluate (limit I above) P ρ) types τ args h=
      (FunctionalSpineActionsProof.markedAction f σ base extraTypes ht extras).scan (limit I above) P ρ (fun {_} _ => false) types τ args h := by
  rw [withSuffix _ types τ args h hn]
  simp only [FunctionalSpineActionsProof.markedAction,FunctionalSpineActionsProof.assembleAction,
    functionalScan,dif_neg hn]
  exact limitCurrentTuple above f σ P (markedState f base extraTypes ht extras (limit I above) P ρ)
    (suffixOf σ.val types τ h hn) args

theorem fullApplication : ActualLimitApplicationTargets.FullApplication := by
  intro Symbol inst arity I above dec Γ σ q P ρ types τ args h
  by_cases hn : types=[]
  · exact emptyApplication (action q) (limit I above) P ρ (fun {_} _ => false) types τ args h hn
  · rcases q with ⟨q,hq⟩
    cases q with
    | var v =>
      change applyWith (ρ v) types τ args h=variableScan v (limit I above) P ρ (fun {_} _ => false) types τ args h
      simp [variableScan]
    | lam body =>
      exact lambdaApplication body (buildTerm I body ⟨hq.1.2.2,hq.2⟩) (limit I above) P ρ types τ args h hn
    | ordinary f base =>
      exact ordinaryApplication ⟨f,hq.2.1⟩ (buildArguments I base ⟨hq.1.2,hq.2.2⟩)
        (limit I above) P ρ types τ args h hn
    | marked f output base extraTypes extras =>
      exact markedApplication above ⟨f,hq.2.1⟩ ⟨σ,hq.1.1⟩
        (buildArguments I base ⟨hq.1.2.1,hq.2.2.1⟩) extraTypes (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩)
        (buildArguments I extras ⟨hq.1.2.2,hq.2.2.2⟩) P ρ types τ args h hn

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationProof
