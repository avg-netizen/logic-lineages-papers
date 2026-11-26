module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureFinalGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalCanonicalizedObjectTypedTransportSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureGraphsProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalFinalVariableCanonicalSupportProof (iffForward iffBackward)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open GuardedErasureFinalGraphsProof VariableSourceErasureTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem sameFinalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    Integration.preparedKernelFinalInputs p H G W P =
      OriginalLambdaTraversalSelection.finalInputs
        (OriginalFinalGuardedRank.refined (preparedSeed p H G W P) H G W) := rfl

theorem sameFinalData (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    finalData p H G W P = OriginalLambdaTraversalSelection.finalData
      (OriginalFinalGuardedRank.refined (preparedSeed p H G W P) H G W) := rfl

/-- Original typed Object exposure supplies the old literal raw source.
There is no source/recognizer premise at the erased variable. -/
theorem sourceFromOriginal (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index parameter : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.Premise (preparedSeed p H G W P) H G W context tau
        source target witness gamma extended packed raw domain (suc index))))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) extended))) :
    Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) packed parameter)) := by
  let seed := preparedSeed p H G W P
  let p0 := OriginalRankGuardedRepresentative.guardedInputs H G W seed
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have shape := andLeft (andRight (andRight h))
  have object := andRight (andRight (andRight shape))
  have ht := OriginalCanonicalizedObjectTypedTransportSupportProof.outerRecover
    p0 H G W context typ source extended packed parameter
    (andLeft h) (andLeft (andRight h)) object hp
  have parts := InternalOriginalUniformDescentSelectionInternalProof.typedRecover
    (finalData p H G W P).oldRepresentative
    (InternalOriginalUniformDescentSelection.validity (finalData p H G W P))
    (finalData p H G W P).member packed typ parameter ht
  exact iffForward (Integration.FinalErasureProof.finalSource p H G W P body alpha Delta (numeral 1)
    (Fin.cons packed (Fin.cons parameter Fin.elim0))) (andLeft (andRight parts))

theorem actualWindow (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat) (raw parameter gamma : OTerm alpha)
    (hw : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta
      (graph2 InternalPairing.pairing parameter (numeral context) gamma))) :
    Nonempty (Derivation body Delta
      (OriginalVariableRepresentative.windowGraph (Integration.preparedKernelFinalInputs p H G W P).window raw parameter)) :=
  iffBackward (OriginalFinalVariableWeakeningSupportProof.contextCheckEquation
    (Integration.preparedKernelFinalInputs p H G W P).window
    (numeral 1) raw parameter (numeral context) gamma hp) hw

/-- Literal variable fixed output at the SAME final fold; arbitrary new Gamma
source validity and active window are actual graphs, not canonical premises. -/
theorem variableFoldSelf (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat)
    (packed raw typ index parameter gamma : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor raw index)))
    (hpack : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) packed parameter)))
    (hw : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (numeral context) gamma))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) packed packed parameter)) := by
  let r := OriginalFinalGuardedRank.refined (preparedSeed p H G W P) H G W
  have hD := OriginalFinalVariableCanonicalSupportProof.finalVariableSelectedData r
  change finalData p H G W P = _ at hD
  have valid := sourceToFinal p H G W P packed parameter hs
  rw [hD] at valid
  have window := actualWindow p H G W P context packed parameter gamma hw hp
  have fixed := OriginalFinalVariableCanonicalSupportProof.variableFixed
    (OriginalFinalVariableCanonicalSupportProof.finalVariableBase r) r.window
    packed raw typ index parameter hv hpack valid window
  rw [← hD] at fixed
  exact fixed

/-- The actual bottom-preserving full fold and its original type law force
the literal bottom itself. No general Object cancellation is invoked. -/
theorem bottomFoldSelf (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (context : Nat) (packed typ parameter gamma : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode packed typ)))
    (hs : Nonempty (Derivation body Delta (graph2 (literalSource p H G W) (numeral 1) packed parameter)))
    (hw : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter (numeral context) gamma))) :
    Nonempty (Derivation body Delta
      (InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) packed packed parameter)) := by
  let D := finalData p H G W P
  let f := Integration.preparedKernelFinalInputs p H G W P
  have valid := sourceToFinal p H G W P packed parameter hs
  have window := actualWindow p H G W P context packed parameter gamma hw hp
  apply programCases (InternalParameterizedCanonicalResultFold.foldN D)
    (Fin.cons packed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta out hj hn
  rw [InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename]
  simp only [consTermRename,emptyRename] at hn
  have hb' := renameInto hb j Theta hj
  have hs' := renameInto valid j Theta hj
  have hw' := renameInto window j Theta hj
  rw [graph1Rename] at hb'
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs'
  simp only [OriginalVariableRepresentative.windowGraph,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hout := OriginalNeutralQuotientBottomProof.bottomThroughFold f.base f.window
    out (packed.relabel j) (typ.relabel j) (parameter.relabel j) hw' hs' hn hb'
  have he := valueUnique BottomRepresentative.bottomCode out (packed.relabel j)
    (Fin.cons (typ.relabel j) Fin.elim0) hout hb'
  exact outputTransport (InternalParameterizedCanonicalResultFold.foldN D) out (packed.relabel j)
    (Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureGraphsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureGraphsProof
