module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalLambdaConstructorGraphSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalSquareRootArithmeticSupportProof (orderRight)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (arityCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem positiveAt (input count value : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input)))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw (suc value) input))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z count)) := by
  obtain ⟨he⟩ := valueUnique OriginalStructuralNodeSize.raw (suc value) count ![input] hv hp
  exact ⟨orderRight z he (InternalQuotientComparisonProof.zeroLessSuccessor value)⟩

def unaryQueries : Fin 2 → Program 1 :=
  ![firstOf (.projection 0), .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => firstOf (.projection 0))]

theorem unaryPositive (input count : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) input)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z count)) := by
  apply queryCases unaryQueries (Fin.cons input Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [InternalLessThan.strictLess,orderRename,zRelabel]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ha' hp'
  have hc := unaryRecover OriginalStructuralNodeSize.raw (firstOf (.projection 0)) (ys 1) (ys 0)
    ![input.relabel j] (hq 1) (hq 0)
  exact positiveAt (input.relabel j) (count.relabel j) (ys 1) hp'
    (OriginalStructuralNodeSizeInternalRecurrenceProof.unary (input.relabel j) (ys 0) (ys 1) ha' (hq 0) hc)

def binaryQueries : Fin 4 → Program 1 :=
  ![firstOf (.projection 0), secondOf (.projection 0),
    .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => firstOf (.projection 0)),
    .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => secondOf (.projection 0))]

theorem binaryPositive (input count : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) input)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z count)) := by
  apply queryCases binaryQueries (Fin.cons input Fin.elim0) _
  intro beta j ys Theta hj hq
  simp only [InternalLessThan.strictLess,orderRename,zRelabel]
  simp only [consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  have hp' := renameInto hp j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ha' hp'
  have hf := unaryRecover OriginalStructuralNodeSize.raw (firstOf (.projection 0)) (ys 2) (ys 0)
    ![input.relabel j] (hq 2) (hq 0)
  have hs := unaryRecover OriginalStructuralNodeSize.raw (secondOf (.projection 0)) (ys 3) (ys 1)
    ![input.relabel j] (hq 3) (hq 1)
  exact positiveAt (input.relabel j) (count.relabel j) (add (ys 2) (ys 3)) hp'
    (OriginalStructuralNodeSizeInternalRecurrenceProof.binary (input.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
      ha' (hq 0) (hq 1) hf hs)

theorem positive (input count : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess z count)) := by
  apply arityCases input
  · intro beta j Theta hj ha
    simp only [InternalLessThan.strictLess,orderRename,zRelabel]
    have hp' := renameInto hp j Theta hj
    rw [graph1Rename] at hp'
    exact positiveAt (input.relabel j) (count.relabel j) z hp'
      (OriginalStructuralNodeSizeInternalLeafProof.leaf (input.relabel j) ha)
  · intro beta j Theta hj ha
    simp only [InternalLessThan.strictLess,orderRename,zRelabel]
    have hp' := renameInto hp j Theta hj
    rw [graph1Rename] at hp'
    exact unaryPositive (input.relabel j) (count.relabel j) ha hp'
  · intro beta j Theta hj ha
    simp only [InternalLessThan.strictLess,orderRename,zRelabel]
    have hp' := renameInto hp j Theta hj
    rw [graph1Rename] at hp'
    exact binaryPositive (input.relabel j) (count.relabel j) ha hp'

theorem actualPositive : OriginalStructuralNodeSizePositiveTargets.Positive := by
  intro body alpha Delta input count
  obtain ⟨h⟩ := positive (body := body) (Delta := graph1 OriginalStructuralNodeSize.raw count input :: Delta)
    input count ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveProof
