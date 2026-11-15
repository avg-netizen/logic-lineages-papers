module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.CapabilityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Recompute at the actual published root, then use only its own theory inclusion. -/
theorem compiler {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k) (ht : ArithmeticTemplateEvaluation.Arithmetic t)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 CompilerCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx values index fuel
 have hout := CumulativeUniformRule12Registry.CapabilityProof.compiler
  (root f lhs rhs pF pR old a baseX) f lhs rhs t ht old a (SaturatedAxiomLeaf.saturated baseX) I ctx values index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
/-- Recompute at the actual published root, then use only its own theory inclusion. -/
theorem equality {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 EqualityCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx raw index fuel
 have hout := CumulativeUniformRule12Registry.CapabilityProof.equality
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I ctx raw index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
/-- Recompute at the actual published root, then use only its own theory inclusion. -/
theorem fullFormula {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 FullFormulaCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx raw index fuel
 have hout := CumulativeUniformRule12Registry.CapabilityProof.fullFormula
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I ctx raw index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
/-- Recompute at the actual published root, then use only its own theory inclusion. -/
theorem retention {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 RetentionCapability f lhs rhs t old a baseX pF pR I := by
 intro ctx index fuel context formula code
 have hout := CumulativeUniformRule12Registry.CapabilityProof.retention
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I ctx index fuel context formula code
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
/-- Only actual new-root Theory inclusion into this same tuple's source S. -/
theorem uniform13 {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 Uniform13Capability f lhs rhs t old a baseX pF pR I := by
 intro ctx formula replacement index fuel
 have hout := CumulativeUniformRule12Registry.CapabilityProof.uniform13
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I ctx formula replacement index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
/-- Only actual new-root Theory inclusion into this same tuple's source S. -/
theorem uniform12 {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : CumulativeUniformRule12Registry.JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) :
 Uniform12Capability f lhs rhs t old a baseX pF pR I := by
 intro ctx formula left right index fuel
 have hout := CumulativeUniformRule12Registry.CapabilityProof.uniform12
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I ctx formula left right index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.CapabilityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.CapabilityProof
