module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidity
open OriginalTransparentLambdaValidityInternalNormalizationSupportProof
open OriginalTransparentLambdaValidityInternalBottomParameterProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Original pairing totality opens every raw parameter and builds its
context-only companion internally. The contextual slice is a previously
proved graph law, instantiated below for each exact local validator. -/
theorem normalizationInvariant (old : Program 2)
    (slice : ∀ (beta : Type) (Delta : List (Formula beta))
      (out raw parameter context gammaCode contextOnly : OTerm beta),
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gammaCode)) →
      Nonempty (Derivation body Delta (graph2 InternalPairing.pairing contextOnly context z)) →
      Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (numeral 1) raw)) →
      Nonempty (Derivation body Delta
        ((graph2 old out raw parameter).iff (graph2 old out raw contextOnly))))
    (out raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (BottomParameter.normalized old) out raw parameter).iff (graph2 old out raw parameter))) := by
  apply queryCases ![InternalUnpair.left,InternalUnpair.right] (Fin.cons parameter Fin.elim0) _
  intro beta j ys Delta hj hq
  change Nonempty (Derivation body Delta
    (((graph2 (BottomParameter.normalized old) out raw parameter).relabel j).iff
      ((graph2 old out raw parameter).relabel j)))
  simp only [graph2Rename]
  simp only [consTermRename,emptyRename] at hq
  have hp := reconstructPair (parameter.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
  apply programCases InternalPairing.pairing (Fin.cons (ys 0) (Fin.cons z Fin.elim0)) _
  intro gamma k Theta contextOnly hk hz
  change Nonempty (Derivation body Theta
    (((graph2 (BottomParameter.normalized old) (out.relabel j) (raw.relabel j) (parameter.relabel j)).relabel k).iff
      ((graph2 old (out.relabel j) (raw.relabel j) (parameter.relabel j)).relabel k)))
  simp only [graph2Rename]
  have hp' := renameInto hp k Theta hk
  simp only [graph2Rename] at hp'
  simp only [consTermRename,emptyRename,zRelabel] at hz
  let B := BottomRepresentative.bottomGraph (numeral 1) ((raw.relabel j).relabel k)
  have hs : Nonempty (Derivation body Theta
      (B.imp ((graph2 old ((out.relabel j).relabel k) ((raw.relabel j).relabel k)
          ((parameter.relabel j).relabel k)).iff
        (graph2 old ((out.relabel j).relabel k) ((raw.relabel j).relabel k) contextOnly)))) := by
    obtain ⟨h⟩ := slice gamma (B :: Theta) ((out.relabel j).relabel k) ((raw.relabel j).relabel k)
      ((parameter.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k) contextOnly
      (addAssumption hp' B) (addAssumption hz B) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  exact normalizationAtCoordinates old ((out.relabel j).relabel k) ((raw.relabel j).relabel k)
    ((parameter.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k) contextOnly hp' hz hs

theorem actualOriginalTransparentInternalBottomNormalization :
    OriginalTransparentLambdaValidityInternalTargets.ActualOriginalTransparentInternalBottomNormalization := by
  intro body rawData alpha out raw parameter
  constructor
  · exact normalizationInvariant (sourceValidator rawData)
      (fun beta Delta out raw parameter context gammaCode contextOnly hp hz hb =>
        sourceBottomParameter rawData out raw parameter context gammaCode contextOnly hp hz hb)
      out raw parameter
  · exact normalizationInvariant (targetValidator rawData)
      (fun beta Delta out raw parameter context gammaCode contextOnly hp hz hb =>
        targetBottomParameter rawData out raw parameter context gammaCode contextOnly hp hz hb)
      out raw parameter
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationProof
