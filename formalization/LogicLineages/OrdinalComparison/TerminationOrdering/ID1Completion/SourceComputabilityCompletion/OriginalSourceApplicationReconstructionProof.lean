module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionInputsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalOriginalUniformApplicationTypingApplicationProof (typedGraphRename)
open InternalParameterizedCanonicalResultFoldSyntaxProof (applicationGraphRename)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion OriginalSourceApplicationReconstruction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Bind both new Objects by two original pairing queries. Every retained
input and raw target graph is transported through the SAME continuation. -/
theorem eliminate (oldComp : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) :
    ApplicationReconstruction data window
      (Outer.computability oldComp data window oldVertex oldResult) context := by
  intro body alpha Gamma sigma tau F A X gammaCode function argument out parameter
    targetFunction vertex psi hinput hfunction hj next
  let queries : Fin 2 → Program 3 :=
    Fin.cons (pairOf (.projection 0) (.projection 1))
      (Fin.cons (pairOf (.projection 0) (.projection 2)) Fin.elim0)
  apply queryCases queries
    (Fin.cons gammaCode (Fin.cons targetFunction (Fin.cons vertex Fin.elim0))) psi
  intro beta j ys Delta hinc hqueries
  simp only [consTermRename,emptyRename] at hqueries
  let xs : Fin 3 → OTerm beta := Fin.cons (gammaCode.relabel j)
    (Fin.cons (targetFunction.relabel j) (Fin.cons (vertex.relabel j) Fin.elim0))
  have hG := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (gammaCode.relabel j) (targetFunction.relabel j) xs
    (hqueries 0) (projectionValue 0 xs) (projectionValue 1 xs)
  have hV := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2)
    (ys 1) (gammaCode.relabel j) (vertex.relabel j) xs
    (hqueries 1) (projectionValue 0 xs) (projectionValue 2 xs)
  have hinput' := renameInto hinput j Delta hinc
  rw [OriginalSourceNeutralApplicationSyntaxProof.recoveredRename] at hinput'
  have hfunction' := renameInto hfunction j Delta hinc
  simp only [typedGraphRename,numeralRename] at hfunction'
  have hj' := renameInto hj j Delta hinc
  simp only [applicationGraphRename,numeralRename] at hj'
  have hrecovered := OriginalSourceApplicationReconstructionInputsProof.recoveredAt
    oldComp data window oldVertex oldResult context sigma tau
    (F.relabel j) (A.relabel j) (X.relabel j) (gammaCode.relabel j)
    (function.relabel j) (argument.relabel j) (out.relabel j) (parameter.relabel j)
    (targetFunction.relabel j) (vertex.relabel j) (ys 0) (ys 1)
    hinput' hfunction' hj' hG hV
  exact next beta j Delta hinc (ys 0) (ys 1) hrecovered

theorem actualOriginalSourceApplicationReconstruction :
    OriginalSourceApplicationReconstructionTargets.ActualOriginalSourceApplicationReconstruction := by
  intro data window oldComp oldVertex oldResult context
  exact eliminate oldComp data window oldVertex oldResult context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionProof.actualOriginalSourceApplicationReconstruction
