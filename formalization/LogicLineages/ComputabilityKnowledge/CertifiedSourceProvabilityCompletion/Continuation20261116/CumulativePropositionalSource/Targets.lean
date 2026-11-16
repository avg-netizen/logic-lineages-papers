module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.HelperCapabilities
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- All six prior runtime capabilities, six packages, K/S certificates and seven
current-root helper contracts share ONE actual new tuple and global installation.
No equality with a previously selected source tuple is asserted or assumed. -/
def OnePublishedSource : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k),
 ArithmeticTemplateEvaluation.Arithmetic t →
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag btag : Nat),
 ∃ I : JointInstallation
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 I.currentK.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentS.verifierTag = GorbowNamedInternalProvability.checkerTag pF ∧
 I.currentK.coreTag = I.currentS.coreTag ∧
 I.currentK.iteratorTag = I.currentS.iteratorTag ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 (nodes (root f lhs rhs pF pR old a baseX))[btag]? =
  some ⟨6,carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩ ∧
 (nodes (root f lhs rhs pF pR old a baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 LiteralValidatedSource.Retained (logical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages f lhs rhs old a baseX offset pF pR c mtag xtag ∧
 CompilerCapability f lhs rhs t old a baseX pF pR I ∧
 EqualityCapability f lhs rhs t old a baseX pF pR I ∧
 FullFormulaCapability f lhs rhs t old a baseX pF pR I ∧
 RetentionCapability f lhs rhs t old a baseX pF pR I ∧
 PriorRetentionCapability f lhs rhs t old a baseX pF pR I ∧
 Uniform13Capability f lhs rhs t old a baseX pF pR I ∧
 Uniform12Capability f lhs rhs t old a baseX pF pR I ∧
 PropositionalCapability f lhs rhs t old a baseX pF pR I ∧
 SeedCapability f lhs rhs t old a baseX pF pR c I ∧
 SpecializationCapability f lhs rhs t old a baseX pF pR c I ∧
 SpecializationTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 CompositionTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 CompositionCapability f lhs rhs t old a baseX pF pR c I ∧
 RecursionBaseTraceCapability f lhs rhs t old a baseX pF pR c I ∧
 RecursionBaseCapability f lhs rhs t old a baseX pF pR c I
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Targets
