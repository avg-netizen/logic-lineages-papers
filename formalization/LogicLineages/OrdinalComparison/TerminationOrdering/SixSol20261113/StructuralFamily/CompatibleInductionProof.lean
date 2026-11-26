module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleVariableProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleInductionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualLimitSubstitutionSupportProof ActualLimitSubstitutionLambdaProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem substitutionPair (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (hq : Confined I q) (Δ : List Ty) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s),
      Related M s hs (buildTerm I q hq)
        (buildTerm I (substituteTerm q s) (ConfinedSubstitutionProof.substitutionClosure Symbol inferInstance arity I Γ Δ τ q s hq hs)) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (ha : ArgumentsConfined I args) (Δ : List Ty)
      (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s),
      ArgumentsRelated M s hs (buildArguments I args ha)
        (buildArguments I (substituteArguments args s) (ConfinedSubstitutionProof.argumentClosure Symbol inferInstance arity I Γ Δ types args s ha hs))) with
  | var v =>
    intro hq Δ s hs
    exact CompatibleVariableProof.variableRelated M hcompat v hq.1 s hs
  | lam body ih =>
    intro hq Δ s hs
    exact lambdaRelated M s hs body (buildTerm I body ⟨hq.1.2.2,hq.2⟩) _
      (ih ⟨hq.1.2.2,hq.2⟩ _ (liftSubstitution s) (ConfinedSubstitutionProof.liftedRange Symbol inferInstance arity I _ Δ _ s hs))
  | ordinary f base ih =>
    intro hq Δ s hs
    exact ordinaryRelated M s hs ⟨f,hq.2.1⟩ _ _ (ih ⟨hq.1.2,hq.2.2⟩ Δ s hs)
  | marked f output base types extras ihb ihe =>
    intro hq Δ s hs
    exact markedRelated M s hs ⟨f,hq.2.1⟩ ⟨output,hq.1.1⟩ _ _ types
      (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩) _ _
      (ihb ⟨hq.1.2.1,hq.2.2.1⟩ Δ s hs) (ihe ⟨hq.1.2.2,hq.2.2.2⟩ Δ s hs)
  | nil =>
    intro P ρ η hag
    funext i
    exact Fin.elim0 i
  | cons q rest ihq ihr =>
    rename_i ha Δ s hs
    intro P ρ η hag
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (ihq ⟨ha.1.1,ha.2.1⟩ Δ s hs P ρ η hag).1
    · exact congrFun (ihr ⟨ha.1.2,ha.2.2⟩ Δ s hs P ρ η hag) j

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleInductionProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleInductionProof
