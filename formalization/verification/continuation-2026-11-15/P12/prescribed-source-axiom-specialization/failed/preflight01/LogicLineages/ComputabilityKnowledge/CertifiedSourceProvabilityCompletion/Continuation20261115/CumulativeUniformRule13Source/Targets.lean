module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- All prior and current interfaces, source facts, six packages and five runtime
capabilities share ONE newly selected actual tuple/global installation. -/
def OnePublishedSource : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k),
 ArithmeticTemplateEvaluation.Arithmetic t →
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag btag : Nat),
 ∃ I : CumulativeUniformRule13Registry.JointInstallation
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.current.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,CumulativeUniformRule13Registry.carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 LiteralValidatedSource.Retained (logical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages f lhs rhs old a baseX offset pF pR c mtag xtag ∧
 CompilerCapability f lhs rhs t old a baseX pF pR I ∧
 EqualityCapability f lhs rhs t old a baseX pF pR I ∧
 FullFormulaCapability f lhs rhs t old a baseX pF pR I ∧
 RetentionCapability f lhs rhs t old a baseX pF pR I ∧
 UniformCapability f lhs rhs t old a baseX pF pR I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Source.Targets
