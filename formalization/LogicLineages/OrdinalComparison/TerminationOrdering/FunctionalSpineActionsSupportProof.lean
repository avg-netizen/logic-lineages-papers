module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsSupportProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions TypedExtraDownsets FullTuplePacking OrdinaryFunctionalValue FunctionalSpineActions

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem argumentsMonotone {Γ types : List Ty} (A : ArgumentActions I Γ types)
    {M N : Constructors I} {P : World I} {ρ η : Environment I Γ P} (hMN : M ≤ N) (hρη : EnvLE ρ η) :
    evaluateArguments A M P ρ ≤ evaluateArguments A N P η := by
  intro i
  exact (A i).evaluateMonotone M N P ρ η hMN hρη

theorem argumentsRestriction {Γ types : List Ty} (A : ArgumentActions I Γ types)
    (M : Constructors I) {P Q : World I} (h : Extends P Q) (ρ : Environment I Γ P) :
    weakenValues h (evaluateArguments A M P ρ)=evaluateArguments A M Q (restrict h ρ) := by
  funext i
  exact (A i).evaluateNatural M P Q h ρ

theorem packedDomination (types : List Ty) (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I)
    {P : World I} (v w : Values I types P) (h : v ≤ w) :
    TypedExtraAppend.Dominated (packArguments types ht v) (packArguments types ht w) := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,(TypedExtraDownsetsProof.packedSame _ _ _).mpr (h i)⟩

theorem packedRestriction (types : List Ty) (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I)
    {P Q : World I} (h : Extends P Q) (v : Values I types P) :
    (packArguments types ht v).map (packedWeaken h)=packArguments types ht (weakenValues h v) := by
  simp only [packArguments,List.map_ofFn]
  rfl

theorem ordinaryStateMonotone {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    {M N : Constructors I} {P : World I} {ρ η : Environment I Γ P} (hMN : M ≤ N) (hρη : EnvLE ρ η) :
    ordinaryState f base M P ρ ≤ ordinaryState f base N P η :=
  ⟨argumentsMonotone base hMN hρη,le_rfl⟩

theorem ordinaryStateRestriction {Γ : List Ty} (f : HeadIndex I) (base : ArgumentActions I Γ (headArguments arity f.val))
    (M : Constructors I) {P Q : World I} (h : Extends P Q) (ρ : Environment I Γ P) :
    (inputFamily I f).restrict h (ordinaryState f base M P ρ)=ordinaryState f base M Q (restrict h ρ) := by
  apply Prod.ext
  · exact argumentsRestriction base M h ρ
  · exact OrdinaryFunctionalValueProof.emptyRestriction h

theorem stateMonotone : FunctionalSpineActionsTargets.StateMonotone := by
  intro Symbol inst arity I Γ f base extraTypes ht extras M N P ρ η hMN hρη
  change FunctionalTupleBuilder.appendInput (ordinaryState f base M P ρ) (packArguments extraTypes ht (evaluateArguments extras M P ρ)) ≤
    FunctionalTupleBuilder.appendInput (ordinaryState f base N P η) (packArguments extraTypes ht (evaluateArguments extras N P η))
  exact FunctionalTupleBuilderProof.appendInputMonotone (ordinaryStateMonotone f base hMN hρη)
    (packedDomination extraTypes ht _ _ (argumentsMonotone extras hMN hρη))

theorem stateRestriction : FunctionalSpineActionsTargets.StateRestriction := by
  intro Symbol inst arity I Γ f base extraTypes ht extras M P Q h ρ
  change (inputFamily I f).restrict h (FunctionalTupleBuilder.appendInput (ordinaryState f base M P ρ) (packArguments extraTypes ht (evaluateArguments extras M P ρ))) =
    FunctionalTupleBuilder.appendInput (ordinaryState f base M Q (restrict h ρ)) (packArguments extraTypes ht (evaluateArguments extras M Q (restrict h ρ)))
  rw [FunctionalTupleBuilderProof.appendInputRestriction,ordinaryStateRestriction,packedRestriction,argumentsRestriction]

theorem fullTupleScanEquation : FunctionalSpineActionsTargets.FullTupleScanEquation := by
  intro Symbol inst arity I Γ f σ e state M P ρ mask types τ args h hne
  simp only [functionalScan,dif_neg hne]

theorem evaluationEquations : FunctionalSpineActionsTargets.EvaluationEquations := by
  intro Symbol inst arity I Γ f σ base extraTypes ht extras M P ρ
  exact ⟨rfl,rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.FunctionalSpineActionsSupportProof
