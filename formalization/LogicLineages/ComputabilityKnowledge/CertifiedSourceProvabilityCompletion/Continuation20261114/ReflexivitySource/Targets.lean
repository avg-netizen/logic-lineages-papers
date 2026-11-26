module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivitySource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivitySource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB
open SixSol20261113 SixSol20261113.LiteralCheckerAuxiliaries
/-- Fresh, explicitly refined source selection, retaining the ENTIRE accepted
Retained package at identical witnesses, plus the actual original MP constructor.
The old logical leaf is calibrated on every raw input; its explicit refinement is
chosen before pF/pR/c. No identity with an older existential source is asserted.
Quote registry installation, final source reflexivity, HB3 remain separate. -/
def RetainedReflexivitySource : Prop :=
 ∃ (old arithmetic : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag : Nat),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (logical old) arithmetic (SaturatedAxiomLeaf.saturated baseX)
   offset pF pR c tagCK pCK tagG pG ∧
 (nodes (GorbowSourceRegistryPadding.root
   (augmented pF (LiteralKernelSource.verifier LiteralSourceCoreMP.valid (logical old)
    arithmetic (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer)) pR))[mtag]? =
   some ⟨4,LiteralRawMP.constructor⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivitySource.Targets
