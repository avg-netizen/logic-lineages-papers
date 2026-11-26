module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.NodeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.AxiomPackageProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open SixSol20261112 LiteralCheckerAuxiliaries

theorem axiomPackage (l a : Program 1) (baseX : Program 3) (pF pR : Program 1) :
 ∃ xtag, Targets.AxiomPackage l a baseX pF pR xtag := by
 obtain ⟨xtag,ht⟩ := NodeProof.actualAxiom l a baseX pF pR
 let q := LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer
 let root := GorbowSourceRegistryPadding.root (augmented pF q) pR
 obtain ⟨h⟩ := SaturatedAxiomLeaf.StatementChecks.internalMonotonicity 4 root xtag baseX ht 4 (.var 0) (.var 1) (.var 2) (.var 3)
 refine ⟨xtag,ht,?_⟩
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) 0 (axiomMonotonicityClause xtag)
  ⟨Fuel.Logic.closeAll h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.AxiomPackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.AxiomPackageProof
