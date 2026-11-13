module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionLambdaProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleVariableProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment
open FullListValueApplication CoherentConstructorLattice OriginalSpineActions
open ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport
open ActualLimitSubstitutionSupportProof
variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
theorem variableRelated (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ Δ : List Ty} {τ : Ty}
    (v : Variable Γ τ) (ht : τ ∈ TypedExtraDownsets.types I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) :
    Related M s hs (OriginalSpineActionsProof.variableAction v) (action ⟨s v,hs v ht⟩) := by
  intro P ρ η ha
  refine ⟨(ha v ht).symm,?_⟩
  intro sourceMask targetMask hc types υ args h
  by_cases hn : types=[]
  · subst types
    cases h
    exact ((action (⟨s v,hs v ht⟩ : ConfinedTerm I Δ υ)).scanEmpty M P η targetMask args).trans
      ((ha v ht).symm.trans ((OriginalSpineActionsProof.variableAction v).scanEmpty M P ρ sourceMask args).symm)
  · cases hv : sourceMask v with
    | false =>
      have hfree := (hc v ht).2 hv
      have hm := SubstitutionEnvironmentSupportProof.maskLocality Symbol inferInstance arity I Δ τ ⟨s v,hs v ht⟩
        M P η targetMask (fun {_} _ => false) hfree types υ args h
      have happ := CompatibleApplicationProof.fullApplication Symbol inferInstance arity I M hcompat Δ τ
        ⟨s v,hs v ht⟩ P η types υ args h
      have he := congrArg (fun a : Value I τ P => applyWith a types υ args h) (ha v ht).symm
      exact hm.trans (happ.symm.trans (he.trans (by simp [OriginalSpineActionsProof.variableAction,variableScan,hn,hv])))
    | true =>
      obtain ⟨w,hw,hm⟩ := (hc v ht).1 hv
      have hq : (⟨s v,hs v ht⟩ : ConfinedTerm I Δ τ)=⟨.var w,⟨ht,trivial⟩⟩ := Subtype.ext hw
      have he := congrArg (fun q : ConfinedTerm I Δ τ => scan q M P η targetMask types υ args h) hq
      exact he.trans (by simp [scan,action,buildTerm,OriginalSpineActionsProof.variableAction,variableScan,hn,hm,hv])

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleVariableProof
