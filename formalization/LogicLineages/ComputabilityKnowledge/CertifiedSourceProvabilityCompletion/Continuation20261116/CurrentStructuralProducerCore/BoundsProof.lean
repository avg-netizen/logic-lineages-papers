module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundInterfaces
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.GuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
theorem select (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (hA : Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c)
 (hn : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 ∃ leafBound compositionBound recursionBound : Nat,
 BoundInterfaces.Leaf installed lhs rhs t old a baseX pF pR c I leafBound ∧
 BoundInterfaces.Composition installed lhs rhs t old a baseX pF pR c I compositionBound ∧
 BoundInterfaces.Recursion installed lhs rhs t old a baseX pF pR c I recursionBound := by
 obtain ⟨lb,hL⟩ := CurrentBasicProducerProgram.StatementChecks.exactSource installed lhs rhs k t old a baseX pF pR c hA hn I
 obtain ⟨cb,hC⟩ := CurrentCompositionProducerCore.StatementChecks.exactSource installed lhs rhs k t old a baseX pF pR c hA hn I
 obtain ⟨rb,hR⟩ := CurrentRecursionProducerCore.StatementChecks.exactAccumulator installed lhs rhs k t old a baseX pF pR c hA hn I
 exact ⟨lb,cb,rb,hL,hC,hR⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundsProof
