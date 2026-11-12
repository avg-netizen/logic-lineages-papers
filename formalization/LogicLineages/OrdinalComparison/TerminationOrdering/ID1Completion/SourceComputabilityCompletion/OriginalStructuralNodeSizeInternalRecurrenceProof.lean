module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRawParametersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraIntroductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open OriginalStructuralNodeSizeInternalMachineExpansionProof (nextCutoff)
open OriginalStructuralNodeSizeInternalLeafProof (rawFromFold)
open OriginalStructuralNodeSizeInternalRawParametersProof (rawAtParameters)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unary (input child count : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) input)))
    (hc : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) child input)))
    (hn : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count child))) :
    Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw (suc count) input)) := by
  apply programCases nextCutoff (Fin.cons z (Fin.cons input Fin.elim0)) _
  intro beta j Theta childK hj hk
  simp only [graph1Rename,sucRelabel]
  simp only [consTermRename,emptyRename,zRelabel] at hk
  have ha' := renameInto ha j Theta hj
  have hc' := renameInto hc j Theta hj
  have hn' := renameInto hn j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ha' hc' hn'
  exact rawFromFold (input.relabel j) (suc (count.relabel j))
    (OriginalStructuralNodeSizeInternalFoldUnaryProof.unaryBackward z z
      (input.relabel j) (child.relabel j) childK (count.relabel j) (suc (count.relabel j))
      (andIntro ha' (andIntro hc' hk))
      (rawAtParameters (child.relabel j) (count.relabel j) z childK hn')
      (OriginalStructuralNodeSizeInternalAlgebraIntroductionProof.unary (input.relabel j) (count.relabel j) z ha'))

theorem binary (input first second firstCount secondCount : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) input)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first input)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second input)))
    (hfc : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstCount first)))
    (hsc : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondCount second))) :
    Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw (suc (add firstCount secondCount)) input)) :=
  rawFromFold input (suc (add firstCount secondCount))
    (OriginalStructuralNodeSizeInternalFoldBinaryProof.binaryBackward z z input first second firstCount secondCount
      (suc (add firstCount secondCount)) (andIntro ha (andIntro hf hs))
      (rawAtParameters first firstCount z z hfc) (rawAtParameters second secondCount z z hsc)
      (OriginalStructuralNodeSizeInternalAlgebraIntroductionProof.binary input firstCount secondCount ha))

theorem actualUnary : OriginalStructuralNodeSizeTargets.InternalUnary := by
  intro body alpha Delta input child count
  let A := graph1 (arityOf (.projection 0)) (suc z) input ⊓
    (graph1 (firstOf (.projection 0)) child input ⊓ graph1 OriginalStructuralNodeSize.raw count child)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := unary input child count (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualBinary : OriginalStructuralNodeSizeTargets.InternalBinary := by
  intro body alpha Delta input first second firstCount secondCount
  let A := graph1 (arityOf (.projection 0)) (suc (suc z)) input ⊓
    (graph1 (firstOf (.projection 0)) first input ⊓
      (graph1 (secondOf (.projection 0)) second input ⊓
        (graph1 OriginalStructuralNodeSize.raw firstCount first ⊓ graph1 OriginalStructuralNodeSize.raw secondCount second)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := binary input first second firstCount secondCount (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andLeft (andRight (andRight (andRight h))))
    (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
