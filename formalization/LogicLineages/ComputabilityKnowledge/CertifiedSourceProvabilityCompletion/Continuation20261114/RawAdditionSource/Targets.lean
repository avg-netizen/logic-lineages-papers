module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Capabilities
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- One finite source is selected BEFORE every runtime raw term/count/certificate.
All prior packages and original singleton families plus genuine addition
computation coexist at identical newest checker/MP/producer witnesses. -/
def OneUniformSource : Prop :=
 ∃ (old oldA : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (xtag : Nat),
 ∃ I : RawAdditionIteration.Installation (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (logical old) (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages old oldA baseX offset pF pR c I.mpTag xtag ∧
 SingletonCapabilities (S pF pR (verifier old oldA baseX)) (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I ∧
 ComputationCapabilities (S pF pR (verifier old oldA baseX)) (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Targets
