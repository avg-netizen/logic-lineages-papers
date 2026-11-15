module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
/-- One genuine source with fixed extra AST admitted before global installation.
All tuple and installation witnesses precede every runtime input. Retained
includes actual source/syntax/CK/fixed-point/real producer facts, not old-trace
retention. No old/new tuple equality or prior compiler capability is asserted. -/
def OnePublishedSource : Prop :=
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag btag : Nat),
 ∃ I : UniformClosedRule13Certificate.Installation (root pF pR old a baseX)
  old a (SaturatedAxiomLeaf.saturated baseX),
 I.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 (nodes (root pF pR old a baseX))[btag]? =
  some ⟨6,UniformClosedRule13Registry.carrier old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 LiteralValidatedSource.Retained (logical old) a (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages old a baseX offset pF pR c mtag xtag ∧
 RuntimeCapability old a baseX pF pR I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Targets
