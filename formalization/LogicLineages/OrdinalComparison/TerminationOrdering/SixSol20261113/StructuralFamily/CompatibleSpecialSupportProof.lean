module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationSupportProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualOriginalApplication OriginalSpineActions LambdaSpineActions ActualOriginalApplicationSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem argumentSubstitution (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (hr : ArgumentsConfined I (substituteArguments args s)) (P : World I)
    (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement M s hs ρ η) :
    argumentValues (substituteArguments args s) hr M P η=argumentValues args ha M P ρ := by
  induction types with
  | nil => funext i; exact Fin.elim0 i
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact CompatibleProof.interpretationSubstitution Symbol inferInstance arity I M hcompat Γ Δ τ
          ⟨q,⟨ha.1.1,ha.2.1⟩⟩ s hs P ρ η he
      · exact congrFun (ih rest ⟨ha.1.2,ha.2.2⟩ ⟨hr.1.2,hr.2.2⟩) j

theorem emptySuccess (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ Δ : List Ty} {σ τ : Ty}
    (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (h : σ=arrows [] τ) (r : MarkedTerm Symbol arity Δ τ) (hr : Confined I r)
    (heq : applyOriginalWith q.val s (.nil : Arguments Symbol arity Δ []) h=some r)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement M s hs ρ η) :
    interpret ⟨r,hr⟩ M P η=scan q M P ρ (fun {_} _ => true) [] τ
      (argumentValues (I := I) (.nil : Arguments Symbol arity Δ []) ⟨trivial,trivial⟩ M P η) h := by
  cases h
  rw [emptyEquation] at heq
  cases Option.some.inj heq
  exact (CompatibleProof.interpretationSubstitution Symbol inferInstance arity I M hcompat Γ Δ τ q s hs P ρ η he).trans
    ((action q).scanEmpty M P ρ (fun {_} _ => true) _).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialSupportProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialSupportProof
