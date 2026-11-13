module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureApplicationTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z eqn)
open OriginalMixedClosedTraceInductionDefinitions OriginalMixedClosedTraceInductionSyntaxProof
open GuardedErasureFinalGraphsProof GuardedErasurePackingProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atCore (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3)
    (path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowPath (literalSource p H G W)
      (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
      (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path)))
    (hf : Nonempty (Derivation body Delta (fields (literalSource p H G W)
      (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
      path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
    Nonempty (Derivation body Delta (result (literalSource p H G W)
      (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
      s t newParam erasedS erasedT)) := by
  let E : Formula alpha := eqn path z
  apply InternalOriginalPairingOrderArithmeticProof.formulaCases E _
  · have h := withHyp hf E
    have hp := outputTransport InternalUnpair.left path z (Fin.cons cert Fin.elim0)
      (show Nonempty (Derivation body (E :: Delta) (eqn path z)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (andLeft h)
    exact GuardedErasureBaseProof.zeroAt p H G W P
      s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT (andIntro hp (andRight h))
  · apply OriginalContextInsertionLengthProof.nonzeroCases path _
      (show Nonempty (Derivation body (E.not :: Delta) E.not) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    intro beta j Theta head tail hj hc
    rw [resultRename]
    have hi' := renameInto (withHyp hi E.not) j Theta hj
    have hf' := renameInto (withHyp hf E.not) j Theta hj
    rw [belowPathRename] at hi'
    rw [fieldsRename] at hf'
    exact OriginalMixedClosedTraceConsProof.atConsGeneric (literalSource p H G W)
      (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
      (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W))
      (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
        GuardedErasureLambdaProof.lambdaBranch p H G W P
          path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hf hg)
      (fun beta Theta path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz =>
        GuardedErasureApplicationTraceProof.applicationBranch p H G W P
          path head tail s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT next out hi hc hf hg hl hr hz)
      (path.relabel j) head tail (s.relabel j) (t.relabel j) (cert.relabel j)
      (oldParam.relabel j) (newParam.relabel j) (gamma.relabel j) (extended.relabel j)
      (d.relabel j) (cutoff.relabel j) (c.relabel j) (erasedS.relabel j) (erasedT.relabel j) hi' hc hf'

/-- The SAME original arithmetic strong-path induction now carries both
certificate facts. All base, lambda and application suppliers are concrete. -/
theorem rows (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) (P : Program 3) (path : OTerm alpha) :
    Nonempty (Derivation body Delta (AtPath (literalSource p H G W)
      (OriginalTransparentMixedDirectBottom.leaf H G (member p) W p.oldStep)
      (pairedLeaf (finalData p H G W P) (finalLeaf p H G W P) (closedChecker p H G W)) path)) := by
  apply OriginalMixedClosedTraceInductionRowsProof.rowsFromCore
  intro beta Theta path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
  exact atCore p H G W P path s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT hi hf
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureInductionProof
