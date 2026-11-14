module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.PrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.NativeProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.SelectionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem supplierSelection : Targets.SupplierSelection := by
  intro n arity
  obtain ⟨hv,hf⟩ := PrimitiveProof.primitiveFields n arity
  have hsel (i : Fin 19) : ∃ U : Program 3,
      ∀ v, evaluate U v = TransparentExchangeLayer.fieldValue n arity i v :=
    Proof.allPrimitiveFunctions 3 _ (hf i)
  let U : Fin 19 → Program 3 := fun i => Classical.choose (hsel i)
  have hU : ∀ i v, evaluate (U i) v = TransparentExchangeLayer.fieldValue n arity i v :=
    fun i => Classical.choose_spec (hsel i)
  obtain ⟨V,hV⟩ := Proof.allPrimitiveFunctions 3 _ hv
  exact ⟨U,V,hU,hV,TransparentExchangeLayer.NativeProof.nativeOptional n arity U V
    (fun i _ _ => hU i) hV⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.SelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.SelectionProof
