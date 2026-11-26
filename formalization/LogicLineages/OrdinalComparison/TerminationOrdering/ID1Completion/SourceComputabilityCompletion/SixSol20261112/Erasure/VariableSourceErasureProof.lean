module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureCertificateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalErasureCertificateContinuationSurvivorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion
open OriginalErasureCertificateContinuationSyntaxProof (survivorRename)
open OriginalVariableErasureCertificateRawProof (bottomCodePair bottomObjectPair eraseObjectPair equalRefl)
open OriginalRawSyntaxTransportInternalPackedProof (erasePackedBackward)
open GuardedErasureFinalGraphsProof VariableSourceErasureTargets VariableSourceErasureSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- All values are actual original constructor outputs. Erased source
validity, C/W, literal final fold outputs and the new positive source
certificate are conclusions of this assembly. The old certificate is arbitrary. -/
theorem atCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (context : Nat) (tau : Ty)
    (source target witness gamma extended packed raw domain index erasedSource erasedTarget
      variableRaw variablePacked bottomRaw bottomPacked oldParam newParam : OTerm alpha)
    (h : Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.Premise (preparedSeed p H G W P) H G W context tau
        source target witness gamma extended packed raw domain (suc index))))
    (hes : Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source)))
    (het : Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)))
    (hvr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableConstructor variableRaw index)))
    (hvp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing variablePacked
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)) variableRaw)))
    (hbr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.bottomConstructor bottomRaw
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))))
    (hbp : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode bottomPacked
      (numeral (NumberedLeastCodeRepresentative.typeNumber tau)))))
    (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam (numeral context) extended)))
    (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam (numeral context) gamma))) :
    Nonempty (Derivation body Delta
      (OriginalErasureCertificateContinuation.SurvivorResult tau source target gamma extended index erasedSource erasedTarget ⊓
        CertificateWitness p H G W P context erasedSource erasedTarget)) := by
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  have shape := andLeft (andRight (andRight h))
  have cons := andLeft shape
  have oldVariable := andLeft (andRight shape)
  have oldPacked := andLeft (andRight (andRight shape))
  have oldObject := andRight (andRight (andRight shape))
  have oldSource := VariableSourceErasureGraphsProof.sourceFromOriginal p H G W P context tau
    source target witness gamma extended packed raw domain index oldParam h hop
  have insertion := OriginalContextInsertionZeroProof.zeroBackward domain gamma extended cons
  have variableErase := OriginalErasureCertificateContinuationSurvivorProof.eraseSuccessor raw variableRaw domain index oldVariable hvr
  have packedErase := erasePackedBackward packed variablePacked typ raw variableRaw domain (numeral 0)
    oldPacked variableErase hvp
  have newSource := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure
    body alpha Delta H G (member p) W packed variablePacked domain (numeral 0) gamma extended
    (numeral context) oldParam newParam insertion packedErase hop hnp oldSource
  have newTargetSource := OriginalInternalBottomSourceProof.bottomSource H G (member p) W body alpha Delta
    variablePacked bottomPacked newParam typ newSource (pairLeft variablePacked typ variableRaw hvp) hbp
  have oldBottom := OriginalErasureCertificateContinuationEndpointProof.targetBottom
    (preparedSeed p H G W P) H G W context tau source target witness gamma extended packed raw domain (suc index) h
  have oldTarget := bottomObjectPair target typ extended bottomPacked hbp oldBottom
  have bottomPair := bottomCodePair bottomPacked bottomRaw typ hbr hbp
  have bottomErase := OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.bottomBackward
    .erase bottomRaw bottomRaw domain (numeral 0) typ hbr (equalRefl bottomRaw)
  have packedBottomErase := erasePackedBackward bottomPacked bottomPacked typ bottomRaw bottomRaw domain (numeral 0)
    bottomPair bottomErase bottomPair
  have sourceObject := eraseObjectPair domain source erasedSource gamma packed extended variablePacked
    oldObject cons packedErase hes
  have targetObject := eraseObjectPair domain target erasedTarget gamma bottomPacked extended bottomPacked
    oldTarget cons packedBottomErase het
  have window : Nonempty (Derivation body Delta
      (graph1 (Integration.preparedKernelFinalInputs p H G W P).window (numeral 1) (numeral context))) := andLeft h
  have sourceFold := VariableSourceErasureGraphsProof.variableFoldSelf p H G W P context
    variablePacked variableRaw typ index newParam gamma hvr hvp newSource window hnp
  have targetFold := VariableSourceErasureGraphsProof.bottomFoldSelf p H G W P context
    bottomPacked typ newParam gamma hbp newTargetSource window hnp
  have certificate := VariableSourceErasureCertificateProof.fromVariable p H G W P context
    newParam gamma variablePacked typ variableRaw index bottomPacked erasedSource erasedTarget
    window hnp hvp hvr newSource hbp sourceFold targetFold sourceObject targetObject
  have retained := OriginalErasureCertificateContinuationSurvivorProof.survivorAt tau
    source target gamma extended packed raw domain index erasedSource erasedTarget
    variableRaw variablePacked bottomRaw bottomPacked shape oldBottom hes het hvr hvp hbr hbp
  exact andIntro retained certificate

/-- Actual constructor queries, before any certificate is introduced.
Inputs [type,index,Context,Gamma,extendedGamma] keep both parameter pairings. -/
def queries : Fin 6 → Program 5 :=
  let varConstructor : Program 5 := .composition OriginalRawSyntaxTransport.variableConstructor (fun _ : Fin 1 => .projection 1)
  ![varConstructor,pairOf (.projection 0) varConstructor,
    .composition OriginalRawSyntaxTransport.bottomConstructor (fun _ : Fin 1 => .projection 0),
    .composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0),
    pairOf (.projection 2) (.projection 4),pairOf (.projection 2) (.projection 3)]

theorem actualOriginalSurvivingVariableSourceErasure : ActualOriginalSurvivingVariableSourceErasure := by
  intro p H G W P body alpha Delta context tau source target witness gamma extended packed raw domain index erasedSource erasedTarget
  let typ : OTerm alpha := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
  let A := OriginalErasureCertificateContinuation.Premise (preparedSeed p H G W P) H G W context tau
      source target witness gamma extended packed raw domain (suc index) ⊓
    (graph1 OriginalRawObjectTransport.eraseObjectRaw erasedSource source ⊓
      graph1 OriginalRawObjectTransport.eraseObjectRaw erasedTarget target)
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation body (A :: Delta)
      (OriginalErasureCertificateContinuation.SurvivorResult tau source target gamma extended index erasedSource erasedTarget ⊓
        CertificateWitness p H G W P context erasedSource erasedTarget)) := by
    let xs : Fin 5 → OTerm alpha := ![typ,index,numeral context,gamma,extended]
    apply queryCases queries xs _
    intro beta j ys Theta hj hq
    simp only [conjunctionRename,survivorRename,witnessRename]
    have h' := renameInto (andLeft ha) j Theta hj
    rw [premiseRename] at h'
    have hes' := renameInto (andLeft (andRight ha)) j Theta hj
    have het' := renameInto (andRight (andRight ha)) j Theta hj
    rw [graph1Rename] at hes' het'
    let typ' : OTerm beta := numeral (NumberedLeastCodeRepresentative.typeNumber tau)
    let xx : Fin 5 → OTerm beta := ![typ',index.relabel j,numeral context,gamma.relabel j,extended.relabel j]
    have hx : (fun i => (xs i).relabel j) = xx := by
      funext i
      exact Fin.cases (numeralRename _ j) (Fin.cases rfl (Fin.cases (numeralRename _ j)
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) i
    rw [hx] at hq
    simp only [queries] at hq
    have hv := unaryRecover OriginalRawSyntaxTransport.variableConstructor (.projection 1)
      (ys 0) (index.relabel j) xx (hq 0) (projectionValue 1 xx)
    have hp := binaryRecover InternalPairing.pairing (.projection 0)
      (.composition OriginalRawSyntaxTransport.variableConstructor (fun _ : Fin 1 => .projection 1))
      (ys 1) typ' (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
    have hb := unaryRecover OriginalRawSyntaxTransport.bottomConstructor (.projection 0)
      (ys 2) typ' xx (hq 2) (projectionValue 0 xx)
    have hbottom := unaryRecover BottomRepresentative.bottomCode (.projection 0)
      (ys 3) typ' xx (hq 3) (projectionValue 0 xx)
    have hop := binaryRecover InternalPairing.pairing (.projection 2) (.projection 4)
      (ys 4) (numeral context) (extended.relabel j) xx (hq 4) (projectionValue 2 xx) (projectionValue 4 xx)
    have hnp := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
      (ys 5) (numeral context) (gamma.relabel j) xx (hq 5) (projectionValue 2 xx) (projectionValue 3 xx)
    exact atCoordinates p H G W P context tau (source.relabel j) (target.relabel j) (witness.relabel j)
      (gamma.relabel j) (extended.relabel j) (packed.relabel j) (raw.relabel j) (domain.relabel j)
      (index.relabel j) (erasedSource.relabel j) (erasedTarget.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) h' hes' het' hv hp hb hbottom hop hnp
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.VariableSourceErasureProof
