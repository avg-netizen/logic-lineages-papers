module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationBaseTagProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableCodecProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Context.EvaluatorChildrenProjectionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
/-- Literal inverse of the original variable root signature, not a new evaluator. -/
def repack : Program 1 := pairOf (leftOf (rightOf (.projection 0)))
 (pairOf (OriginalRawSyntaxTransport.constant 1 0) (rightOf (rightOf (.projection 0))))
theorem actualRepack (R : Program 2) (input parameter root raw data typ index : OTerm alpha)
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 0) input parameter)))
 (hv : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root input parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right raw input)))
 (hd : Nonempty (Derivation body Delta (graph1 InternalUnpair.right data root)))
 (hy : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ data)))
 (hi : Nonempty (Derivation body Delta (graph1 InternalUnpair.right index data))) :
 Nonempty (Derivation body Delta (graph1 repack input root)) := by
 have hb := Context.EvaluatorAlignmentBranchesProof.branch0 R input parameter root ht hv
 have hdata := rightComponent _ _ input parameter root data hd hb
 have htyp := leftComponent _ _ input parameter data typ hy hdata
 have hindex := rightComponent _ _ input parameter data index hi hdata
 let xs : Fin 2 → OTerm alpha := ![input,parameter]
 have hp := projectionValue (0 : Fin 2) xs
 have hraw := unaryValue InternalUnpair.right (.projection 0) raw input xs hr hp
 have htag := unaryRecover InternalUnpair.left OriginalRootObservation.raw (numeral 0) raw xs ht hraw
 have hidx := unaryRecover InternalUnpair.right OriginalRootObservation.raw index raw xs hindex hraw
 have hty := unaryRecover InternalUnpair.left OriginalRootObservation.packed typ input xs htyp hp
 have pr := reconstructPair raw (numeral 0) index htag hidx
 have pi := reconstructPair input typ raw hty hr
 let ys : Fin 1 → OTerm alpha := ![root]
 have pd := unaryValue InternalUnpair.right (.projection 0) data root ys hd (projectionValue 0 ys)
 have pt := unaryValue InternalUnpair.left (rightOf (.projection 0)) typ data ys hy pd
 have pn := unaryValue InternalUnpair.right (rightOf (.projection 0)) index data ys hi pd
 have pc := OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 ys
 have pv := binaryValue InternalPairing.pairing (OriginalRawSyntaxTransport.constant 1 0)
   (rightOf (rightOf (.projection 0))) raw (numeral 0) index ys pr pc pn
 exact binaryValue InternalPairing.pairing (leftOf (rightOf (.projection 0)))
   (pairOf (OriginalRawSyntaxTransport.constant 1 0) (rightOf (rightOf (.projection 0))))
   input typ raw ys pi pt pv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableCodecProof
