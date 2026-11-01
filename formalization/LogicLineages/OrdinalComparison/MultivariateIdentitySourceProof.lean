module
public import LogicLineages.OrdinalComparison.MultivariateIdentitySourceTargets
public import LogicLineages.OrdinalComparison.MultivariateNormalizeProgramProof
public import LogicLineages.OrdinalComparison.MultivariateNormalOutputProof
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeProof
public import LogicLineages.OrdinalComparison.MultivariatePhiCounterProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateIdentitySource

attribute [local irreducible] Phi actualCollapse encodedMultivariateCollectedNormalize

theorem literal_flag_computable : Computable₂ encodedMultivariateLiteralIdentity := by
  have heq : Primrec (fun p : Nat × Nat => decide (p.1=p.2)) := Primrec.eq.decide
  have hl : Computable (fun p : Nat × Nat => encodedMultivariateCollectedNormalize p.1) :=
    MultivariateNormalizeCode.normalization_program.1.comp Computable.fst
  have hr : Computable (fun p : Nat × Nat => encodedMultivariateCollectedNormalize p.2) :=
    MultivariateNormalizeCode.normalization_program.1.comp Computable.snd
  exact heq.to_comp.comp (hl.pair hr)

private theorem literal_flag_correct (E F : MultivariatePositiveExpr) :
    encodedMultivariateLiteralIdentity (multivariatePositiveEncode E) (multivariatePositiveEncode F)=true ↔
      multivariateCollectedNormalize E=multivariateCollectedNormalize F := by
  unfold encodedMultivariateLiteralIdentity
  rw [decide_eq_true_eq,MultivariateNormalizeCode.normalization_program.2 E,
    MultivariateNormalizeCode.normalization_program.2 F]
  exact ⟨fun h => MultivariateCollected.storage.1 h,fun h => congrArg multivariateCollectedCode h⟩

theorem full_identity : Targets.FullActualMultivariateIdentity := by
  refine ⟨MultivariateNormalizeCode.normalization_program.1,literal_flag_computable,
    MultivariatePhiCounter.phi_counter.1,MultivariateIdentityDecision.decision.2.2.1,?_⟩
  intro d E F hE hF
  dsimp only
  refine ⟨MultivariateNormalizeCode.normalization_program.2 E,
    MultivariateNormalizeCode.normalization_program.2 F,
    (MultivariateNormalValidity.full_validity d E hE).1,
    (MultivariateNormalValidity.full_validity d F hF).1,
    MultivariateDirectNormalize.source d E hE,
    MultivariateDirectNormalize.source d F hF,
    literal_flag_correct E F,
    MultivariateDirectNormalize.complete d E F hE hF,?_⟩
  intro hn
  have hnot : encodedMultivariateIdentity (multivariatePositiveEncode E) (multivariatePositiveEncode F)≠true := by
    intro ht
    exact hn ((MultivariateDirectNormalize.complete d E F hE hF).mpr
      ((MultivariateIdentityDecision.decision.2.2.2 d E F hE hF).1.mp ht))
  have hf : encodedMultivariateIdentity (multivariatePositiveEncode E) (multivariatePositiveEncode F)=false :=
    Bool.eq_false_of_not_eq_true hnot
  exact MultivariatePhiCounter.phi_counter.2 d E F hE hF hf

end LogicLineages.OrdinalComparison.MultivariateIdentitySource
