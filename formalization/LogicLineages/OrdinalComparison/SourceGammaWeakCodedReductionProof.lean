module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionAdequacyProof
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionProgramsProof
public import LogicLineages.OrdinalComparison.SourceGammaRestrictedReductionProof
public import LogicLineages.OrdinalComparison.SourceLiteralWeakWrapperCodeProof
public import LogicLineages.OrdinalComparison.SourceGammaLiteralWeakAggregateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof

theorem exactGeneratedQuery : Targets.ExactGeneratedQuery := by
  intro b e
  have he : request b e=((ExistentialPlan.compile (SourceMachineConjunctionPlan.plan b e)).context.length,
      SyntaxCode.encodeTerm (ParametricLiteralWeakWrapper.constantApply (SourceMachineAggregateBridge.aggregate b e).2),
      SyntaxCode.encodeTerm (ParametricLiteralWeakWrapper.identityApply (SourceMachineAggregateBridge.aggregate b e).1)) := by
    unfold request
    rw [(SourceMachineQueryCode.Proof.exactPackaging.2 b e).1]
    dsimp only
    rw [(SourceLiteralWeakWrapperCode.Proof.exactEncoding _ _).2,
      (SourceLiteralWeakWrapperCode.Proof.exactEncoding _ _).1]
    rfl
  refine ⟨he,?_⟩
  unfold output
  rw [he]
  have hg := SourceMachineRawValuations.Proof.groundContexts.2 b e
  apply (SourceGammaRestrictedReduction.Proof.exactSyntaxClass _ hg _ _).mpr
  have hf := SourceMachinePlanFragment.Proof.actualAggregateFragment b e
  have hk := SourceLiteralWeakWrapperCode.Proof.fragmentPreservation _ _ hf.2.2
  have hi := SourceLiteralWeakWrapperCode.Proof.fragmentPreservation _ _ hf.2.1
  have hkl := SourceLiteralWeakWrapperCode.Proof.internalLevelPreservation _ _ hg hf.2.2
  have hil := SourceLiteralWeakWrapperCode.Proof.internalLevelPreservation _ _ hg hf.2.1
  exact ⟨hk.2,hi.1,hkl.2,hil.1⟩

theorem exact_nonhalting (b e : Nat) :
    Member (SourceMachineControlNonperiodicity.gamma b) (output b e) ↔
      ¬SourceBlankMachineSimulation.Halts e := by
  have ha : RawMember (SourceMachineControlNonperiodicity.gamma b) (output b e) ↔
      SourceGammaLiteralWeakAggregate.RawUniversalWeak b e := by
    unfold output
    rw [(exactGeneratedQuery b e).1]
    exact canonicalAdequacy _ _ (SourceMachineRawValuations.Proof.groundContexts.2 b e) _ _
  constructor
  · intro h
    exact (SourceGammaLiteralWeakAggregate.Proof.universalNonhalting b e).mp (ha.mp h.2)
  · intro h
    exact ⟨(exactGeneratedQuery b e).2,ha.mpr
      ((SourceGammaLiteralWeakAggregate.Proof.universalNonhalting b e).mpr h)⟩

theorem fixedNonhaltingReduction : Targets.FixedNonhaltingReduction := by
  intro b
  have hp : Primrec (output b) := uniformPrimitiveRecursive.2.comp (Primrec.const b) Primrec.id
  exact ⟨exact_nonhalting b,output b,hp.to_comp,fun e => (exact_nonhalting b e).symm⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof
