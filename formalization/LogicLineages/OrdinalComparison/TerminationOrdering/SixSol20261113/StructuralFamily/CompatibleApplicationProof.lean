module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleTargets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleApplicationProof
open Compatible
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue ConfinedStructuralInterpretation SourceConstructorIteration ActualLimitApplicationSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem markedApplication (M : Constructors I) (hc : CurrentTupleCompatible M)
    {Γ : List Ty} (f : HeadIndex I) (σ : TypeIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (extraTypes : List Ty) (ht : ∀ τ ∈ extraTypes,τ ∈ TypedExtraDownsets.types I) (extras : ArgumentActions I Γ extraTypes)
    (P : World I) (ρ : Environment I Γ P) (types : List Ty) (τ : Ty) (args : Values I types P)
    (h : σ.val=arrows types τ) (hn : types≠[]) :
    applyWith ((FunctionalSpineActionsProof.markedAction f σ base extraTypes ht extras).evaluate M P ρ) types τ args h=
      (FunctionalSpineActionsProof.markedAction f σ base extraTypes ht extras).scan M P ρ (fun {_} _ => false) types τ args h := by
  rw [withSuffix _ types τ args h hn]
  simp only [FunctionalSpineActionsProof.markedAction,FunctionalSpineActionsProof.assembleAction,
    functionalScan,dif_neg hn]
  exact hc f σ P (markedState f base extraTypes ht extras M P ρ)
    (suffixOf σ.val types τ h hn) args

theorem fullApplication : CompatibleTargets.FullApplication := by
  intro Symbol inst arity I M hc Γ σ q P ρ types τ args h
  by_cases hn : types=[]
  · exact emptyApplication (action q) M P ρ (fun {_} _ => false) types τ args h hn
  · rcases q with ⟨q,hq⟩
    cases q with
    | var v =>
      change applyWith (ρ v) types τ args h=variableScan v M P ρ (fun {_} _ => false) types τ args h
      simp [variableScan]
    | lam body =>
      exact lambdaApplication body (buildTerm I body ⟨hq.1.2.2,hq.2⟩) M P ρ types τ args h hn
    | ordinary f base =>
      exact ordinaryApplication ⟨f,hq.2.1⟩ (buildArguments I base ⟨hq.1.2,hq.2.2⟩)
        M P ρ types τ args h hn
    | marked f output base extraTypes extras =>
      exact markedApplication M hc ⟨f,hq.2.1⟩ ⟨σ,hq.1.1⟩
        (buildArguments I base ⟨hq.1.2.1,hq.2.2.1⟩) extraTypes (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩)
        (buildArguments I extras ⟨hq.1.2.2,hq.2.2.2⟩) P ρ types τ args h hn

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleApplicationProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleApplicationProof
