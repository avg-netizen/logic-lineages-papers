module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableRepresentativeRigidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalFinalPipelineIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof (refl symm trans)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalFinalVariableWeakeningSupportProof
open OriginalTransparentLambdaFinalLogicProof
open InternalOriginalUniformDescentSelection (Data)
open InternalParameterizedCanonicalResultFold (foldN foldGraph sourcePremises)
open OriginalFinalVariableCanonical UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem iffForward {A B : Formula alpha}
    (h : Nonempty (Derivation body Gamma (A.iff B)))
    (ha : Nonempty (Derivation body Gamma A)) : Nonempty (Derivation body Gamma B) := by
  obtain ⟨h⟩ := h
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft h) ha⟩

theorem iffBackward {A B : Formula alpha}
    (h : Nonempty (Derivation body Gamma (A.iff B)))
    (hb : Nonempty (Derivation body Gamma B)) : Nonempty (Derivation body Gamma A) :=
  iffForward (iffReverse h) hb

/-- These are exactly the existing representative wrappers, not a refinement. -/
def finalVariableBase (q : GlobalSourcePackage.Inputs) : Data :=
  OriginalConstructorShape.baseData
    (OriginalFunctionNeutrality.baseData
      (OriginalApplicationSidecar.baseData
        (OriginalLambdaTraversalSelection.preparedData q.base q.window) q.window)
      q.window) q.window

theorem finalVariableSelectedData (q : GlobalSourcePackage.Inputs) :
    OriginalLambdaTraversalSelection.finalData q =
      OriginalVariableRepresentative.selectedData (finalVariableBase q) q.window := by
  rw [OriginalLambdaTraversalFinalPipelineIdentityProof.finalSelectedData]
  rfl

/-- The actual source graph, literal packed type, window and variable tag pay
the accepted full-fold rigidity rule. No fold identity is assumed. -/
theorem variableRigidity (data : Data) (window : Program 1)
    (out raw variableCode typ index parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalVariableRepresentative.selectedData data window)) (numeral 1) raw parameter)))
    (hw : Nonempty (Derivation body Gamma (OriginalVariableRepresentative.windowGraph window raw parameter)))
    (hf : Nonempty (Derivation body Gamma
      (foldGraph (OriginalVariableRepresentative.selectedData data window) out raw parameter))) :
    Nonempty (Derivation body Gamma (equal out raw)) := by
  have ht := packedVariableTag raw variableCode typ index hc hp
  obtain ⟨hvar⟩ := sameAccept OriginalLambdaConstructor.tag (InternalAcceptance.constantZero 1) z
    (Fin.cons raw Fin.elim0) ht (InternalLessThanSupportProof.zeroConstantValue _)
  have heither : Nonempty (Derivation body Gamma
      (graph1 OriginalConstructorLeaf.variableTest (numeral 1) raw ⊔
        graph1 OriginalConstructorLeaf.variableTest (numeral 1) out)) :=
    ⟨InternalQuotientComparisonProof.orLeft hvar⟩
  obtain ⟨h⟩ := OriginalVariableRepresentativeRigidityProof.fullFoldRigidity data window
    body alpha Gamma out raw typ parameter
  obtain ⟨ha⟩ := andIntro hw (andIntro (andIntro hv (pairLeft raw typ variableCode hp))
    (andIntro hf heither))
  exact ⟨Derivation.implicationElimination h ha⟩

/-- Actual totality supplies a fold output; rigidity and output equality
transport make the original raw value itself that output. -/
theorem variableFixed (data : Data) (window : Program 1)
    (raw variableCode typ index parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalVariableRepresentative.selectedData data window)) (numeral 1) raw parameter)))
    (hw : Nonempty (Derivation body Gamma (OriginalVariableRepresentative.windowGraph window raw parameter))) :
    Nonempty (Derivation body Gamma
      (foldGraph (OriginalVariableRepresentative.selectedData data window) raw raw parameter)) := by
  apply programCases (foldN (OriginalVariableRepresentative.selectedData data window))
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta out hj hf
  change Nonempty (Derivation body Theta
    ((graph2 (foldN (OriginalVariableRepresentative.selectedData data window)) raw raw parameter).relabel j))
  rw [graph2Rename]
  have hc' := renameInto hc j Theta hj
  have hp' := renameInto hp j Theta hj
  have hv' := renameInto hv j Theta hj
  have hw' := renameInto hw j Theta hj
  rw [graph1Rename] at hc'
  rw [graph2Rename] at hp'
  simp only [graph2Rename,numeral,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hv'
  simp only [OriginalVariableRepresentative.windowGraph,graph2Rename,
    InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,
    InternalTagArithmeticSyntaxProof.zRelabel] at hw'
  simp only [consTermRename,emptyRename] at hf
  have he := variableRigidity data window out (raw.relabel j) (variableCode.relabel j)
    (typ.relabel j) (index.relabel j) (parameter.relabel j) hc' hp' hv' hw' hf
  exact outputTransport (foldN (OriginalVariableRepresentative.selectedData data window)) out
    (raw.relabel j) (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (by simpa only [equalEqn] using he) hf

/-- All symbolic outputs, including zero, are characterized internally. -/
theorem variableEquation (data : Data) (window : Program 1)
    (out raw variableCode typ index parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hv : Nonempty (Derivation body Gamma
      (graph2 (InternalOriginalUniformDescentSelection.validity
        (OriginalVariableRepresentative.selectedData data window)) (numeral 1) raw parameter)))
    (hw : Nonempty (Derivation body Gamma (OriginalVariableRepresentative.windowGraph window raw parameter))) :
    Nonempty (Derivation body Gamma
      ((foldGraph (OriginalVariableRepresentative.selectedData data window) out raw parameter).iff
        (equal out raw))) := by
  let A := foldGraph (OriginalVariableRepresentative.selectedData data window) out raw parameter
  let B := equal out raw
  obtain ⟨hf⟩ := variableRigidity data window out raw variableCode typ index parameter
    (addAssumption hc A) (addAssumption hp A) (addAssumption hv A) (addAssumption hw A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hfixed := variableFixed data window raw variableCode typ index parameter hc hp hv hw
  have he : Derivation body (B :: Gamma) (eqn out raw) := by
    simpa only [B,equalEqn] using (Derivation.hypothesis List.mem_cons_self : Derivation body (B :: Gamma) B)
  obtain ⟨hb⟩ := outputTransport (foldN (OriginalVariableRepresentative.selectedData data window)) raw out
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) ⟨symm he⟩ (addAssumption hfixed B)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
