module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterPositiveRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterGammaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationPathLiftSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalParameterizedPathCheckerProof
open InternalListCodecDecompositionSupportProof (reconstructNonzero)
open OriginalFinalVariableCanonicalSupportProof (iffForward)
open InternalTagArithmeticSyntaxProof (suc z)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion PositiveSourceExposureTargets PositiveSourceExposureQueries
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Derive first-edge W and BOTH real final fold outputs from the original
positive source certificate, using only actual total query outputs. -/
theorem atQueries (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ys : Fin 11 → OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph1 q.window (numeral 1) (numeral context))))
    (hc : Nonempty (Derivation body Delta
      (InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false context f g path)))
    (hq : ∀ i, Nonempty (Derivation body Delta
      (programGraph (queries i) (ys i) (![f,g,path,numeral context] : Fin 4 → OTerm alpha)))) :
    Nonempty (Derivation body Delta (Fields q context f g path ys)) := by
  let D := OuterSelection.data q.base q.window
  let xs : Fin 4 → OTerm alpha := ![f,g,path,numeral context]
  simp only [queries] at hq
  have hgamma := unaryRecover InternalUnpair.left (.projection 0) (ys 0) f xs
    (hq 0) (projectionValue 0 xs)
  have hx := unaryRecover InternalUnpair.right (.projection 0) (ys 1) f xs
    (hq 1) (projectionValue 0 xs)
  have hy := unaryRecover InternalUnpair.right (.projection 1) (ys 2) g xs
    (hq 2) (projectionValue 1 xs)
  have hp := binaryRecover InternalPairing.pairing (.projection 3) (leftOf (.projection 0))
    (ys 3) (numeral context) (ys 0) xs (hq 3) (projectionValue 3 xs) (hq 0)
  have hhead := unaryRecover InternalListCodec.headCode (.projection 2) (ys 4) path xs
    (hq 4) (projectionValue 2 xs)
  have htail := unaryRecover InternalListCodec.tailCode (.projection 2) (ys 5) path xs
    (hq 5) (projectionValue 2 xs)
  have hvertex := unaryRecover InternalUnpair.left
    (.composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 2))
    (ys 6) (ys 4) xs (hq 6) (hq 4)
  have hquotient := unaryRecover InternalUnpair.right
    (.composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 2))
    (ys 7) (ys 4) xs (hq 7) (hq 4)
  let quotient : Program 4 := rightOf
    (.composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 2))
  have hs := unaryRecover source quotient (ys 8) (ys 7) xs (hq 8) (hq 7)
  have ht := unaryRecover target quotient (ys 9) (ys 7) xs (hq 9) (hq 7)
  have hk := unaryRecover step quotient (ys 10) (ys 7) xs (hq 10) (hq 7)
  have hselectors := andIntro hs (andIntro ht hk)
  have htargetGamma := OuterGammaProof.targetGamma q.oldSrc q.oldComp D (RawScalar.checker D)
    q.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure q.window context f g path
    (ys 0) hgamma hc
  have hraw := OuterPositiveRawProof.rawPositiveRecover q.oldSrc q.oldComp D (RawScalar.checker D)
    q.oldStep BottomRepresentative.bottomTest BottomSpineMeasure.measure q.window context f g path
    (ys 0) (ys 1) (ys 2) (ys 3) hw hgamma hx hy hp hc
  let E := edgeChecker D q.oldStep
  let pathInputs : Fin 4 → OTerm alpha := ![ys 1,ys 2,path,ys 3]
  have outer := conjunctionRecover (PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
    (InternalAcceptance.conjunction (PositiveGuard.spineGuard BottomSpineMeasure.measure)
      (InternalParameterizedPathChecker.checker E true)) pathInputs hraw
  have inner := conjunctionRecover (PositiveGuard.spineGuard BottomSpineMeasure.measure)
    (InternalParameterizedPathChecker.checker E true) pathInputs (andRight outer)
  have hpositive : Nonempty (Derivation body Delta
      (InternalParameterizedPathChecker.positiveGraph E (ys 1) (ys 2) path (ys 3))) := andRight inner
  have hnonzero := InternalParameterizedApplicationPathLiftSupportProof.positiveNonzero
    E (ys 1) (ys 2) path (ys 3) hpositive
  have hcons := reconstructNonzero path (ys 4) (ys 5) hnonzero hhead htail
  have hentry := reconstructPair (ys 4) (ys 6) (ys 7) hvertex hquotient
  have parts := iffForward (positiveCons E (ys 1) (ys 2) path (ys 4) (ys 5)
    (ys 6) (ys 7) (ys 3) hentry hcons) hpositive
  have requirements := UniformCertificateCompletion.SupportProof.checkerRecover D q.oldStep
    (ys 1) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) (ys 3) hselectors (andLeft parts)
  have step := andLeft requirements
  have sourceValidity := (TypingProof.stepParts D q.oldStep (ys 8) (ys 9) (ys 10) (ys 3) step).1
  have sourceFold := TypingProof.sourceFold D (ys 1) (ys 8) (ys 3) sourceValidity
    (andLeft (andRight requirements))
  have targetFold := andRight (andRight requirements)
  exact andIntro
    (andIntro (reconstructPair f (ys 0) (ys 1) hgamma hx)
      (andIntro (reconstructPair g (ys 0) (ys 2) htargetGamma hy) hp))
    (andIntro (andIntro hcons (andIntro hentry
      (andIntro (edgeReconstruction (ys 7) (ys 8) (ys 9) (ys 10) hselectors) hselectors)))
      (andIntro (andIntro step (andIntro sourceFold targetFold)) (andRight parts)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureCoreProof
