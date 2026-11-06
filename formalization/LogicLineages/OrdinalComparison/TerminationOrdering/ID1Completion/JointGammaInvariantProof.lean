module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaComputabilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantProof
open FirstOrder Language Source PositiveArithmeticOperators PositiveArithmeticTransforms
open SourceComputabilityFormulaSupportProof PositiveArithmeticSchemasProof
open JointGammaInvariantSupportProof InternalCalculus JointGammaInvariant

theorem actualOriginalClosurePremise : JointGammaInvariantTargets.ActualOriginalClosurePremise := by
  intro data n arity hcal context α scalar multiset P v
  rw [closurePremise,allScalarTruth]
  have heven (x : Nat) := imp_congr
    (actualOriginalReplacementBranches data n arity hcal context α scalar multiset P v x).1
    (actualTaggedInvariantBranches α scalar multiset P v x).1
  have hodd (x : Nat) := imp_congr
    (actualOriginalReplacementBranches data n arity hcal context α scalar multiset P v x).2
    (actualTaggedInvariantBranches α scalar multiset P v x).2
  constructor
  · intro h
    constructor
    · intro x
      exact (heven x).mp ((generalImpTruth _ _ _ _).mp (h (tagNumber false x)))
    · intro x
      exact (hodd x).mp ((generalImpTruth _ _ _ _).mp (h (tagNumber true x)))
  · rintro ⟨hs,hm⟩ z
    obtain ⟨⟨odd,x⟩,hz,_⟩ := TaggedArithmeticOperatorsProof.tagPartition z
    subst z
    apply (generalImpTruth _ _ _ _).mpr
    cases odd with
    | false => exact (heven x).mpr (hs x)
    | true => exact (hodd x).mpr (hm x)

theorem actualFiniteSourceInvariant : JointGammaInvariantTargets.ActualFiniteSourceInvariant := by
  intro data n arity hcal S multiset P context typ Gamma x
  rw [(actualTaggedInvariantBranches (Fin 2) (window data S) multiset P ![context,typ]
    (ContextUniform.objectCode Gamma x)).1,window,generalRelabelTruth]
  have hv : (Sum.elim ![context,typ] (fun _ : Fin 1 => ContextUniform.objectCode Gamma x)) ∘
      ![Sum.inl (0 : Fin 2),Sum.inl (1 : Fin 2),Sum.inr (0 : Fin 1)] =
      ![context,typ,ContextUniform.objectCode Gamma x] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl
      (fun k => Fin.cases rfl (fun e => Fin.elim0 e) k) j) i
  rw [hv,JointGammaComputabilityProof.actualFiniteWindowCalibration data n arity hcal]
  exact exists_congr (fun tau => and_congr_right (fun _ => and_congr_right
    (fun _ => JointGammaComputabilityFiberProof.actualOriginalComputabilityFibers n arity Gamma P context tau x)))

theorem actualInternalTaggedInduction : JointGammaInvariantTargets.ActualInternalTaggedInduction := by
  intro data context α Gamma scalar multiset t hstep
  exact ⟨InternalCalculusProof.actualInternalInvariantInduction
    (SourcePresentation.sourceBody data context) α Gamma (tagged scalar multiset) hstep,
    InternalCalculusProof.actualInternalInvariantInstance
      (SourcePresentation.sourceBody data context) α Gamma (tagged scalar multiset) t hstep⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantProof
