module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open GuardedErasureFinalGraphsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Deterministic fresh original nil certificate on the surviving variable.
The arbitrary OLD certificate is never required to be recognized. Source,
bottom validity and the entire actual final W are constructed internally. -/
theorem atCertificate (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (s raw index typ t cert parameter : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) s parameter)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s))) :
    Nonempty (Derivation body Delta
      (UniformCertificateCompletion.stepAccepted (finalData p H G W P) (finalLeaf p H G W P)
        s t cert parameter)) := by
  have tag := OriginalFinalVariableWeakeningSupportProof.packedVariableTag s raw typ index hv hp
  have nonbottom := OriginalFinalVariableWeakeningSupportProof.variableNotBottom s tag
  have typeS := pairLeft s typ raw hp
  have closed := OriginalMixedClosedBottomProof.introduction H G (member p) W p.oldStep p.window
    s t cert parameter typ (andIntro hs (andIntro nonbottom (andIntro typeS (andIntro hb hc))))
  have targetSource := OriginalInternalBottomSourceProof.bottomSource H G (member p) W
    body alpha Delta s t parameter typ hs typeS hb
  have path := OriginalTransparentVariableStepHereditaryProof.certificatePath s cert hc
  have actual := GuardedErasureConstructorsProof.atNil p H G W P typ s t cert parameter
    hs targetSource typeS (BottomSourceShapeProof.bottomCodeLeft t typ hb) path closed
  exact andRight actual
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureStepProof
