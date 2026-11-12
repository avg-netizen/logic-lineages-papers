module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open InternalOriginalOrderSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalTwoDeletionInternalDefinitions
open OriginalTwoDeletionInternalSyntaxProof
open OriginalTwoDeletionInternalLambdaProof OriginalTwoDeletionInternalOrdinaryProof
open OriginalTwoDeletionInternalApplicationProof OriginalTwoDeletionInternalConsProof
open OriginalTwoDeletionInternalNumberedProof
open OriginalRawSyntaxTransportInternalParserUnaryProof OriginalRawSyntaxTransportInternalParserBinaryProof
open OriginalRawSyntaxTransportInternalParserNumberedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalTwoDeletionInternalTagsProof OriginalTwoDeletionInternalBindingProof
open OriginalTwoDeletionInternalIntroductionProof OriginalTwoDeletionInternalLeafProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
theorem unaryCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply orCases (arityOneTags raw ha)
  · intro Theta inc ht
    exact lambdaTagCommute raw a b i j upper lower left right (weakenProof hi inc) ht (weakenProof hf inc)
  · intro Theta inc ht
    exact ordinaryTagCommute raw a b i j upper lower left right (weakenProof hi inc) ht (weakenProof hf inc)

theorem binaryCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply orCases (arityTwoTags raw ha)
  · intro Theta inc ht
    exact applicationTagCommute raw a b i j upper lower left right (weakenProof hi inc) ht (weakenProof hf inc)
  · intro Theta inc ht
    apply orCases ht
    · intro Xi inc2 ht2
      exact numberedTagCommute raw a b i j upper lower left right (weakenProof (weakenProof hi inc) inc2) ht2 (weakenProof (weakenProof hf inc) inc2)
    · intro Xi inc2 ht2
      exact consTagCommute raw a b i j upper lower left right (weakenProof (weakenProof hi inc) inc2) ht2 (weakenProof (weakenProof hf inc) inc2)

theorem commutationStep (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply arityCases raw
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
    exact leafCommute (raw.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) ha (andLeft hf') (andLeft (andRight hf'))
      (andLeft (andRight (andRight hf'))) (andLeft (andRight (andRight (andRight hf'))))
      (andRight (andRight (andRight (andRight hf'))))
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hi' := renameInto hi rho Theta hrho
    rw [belowRawRename] at hi'
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
    exact unaryCommute (raw.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' ha hf'
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hi' := renameInto hi rho Theta hrho
    rw [belowRawRename] at hi'
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
    exact binaryCommute (raw.relabel rho) (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' ha hf'

theorem allRawCommutation (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw (fold .erase) raw)) := by
  apply rawInduction (fold .erase) raw
  intro beta Theta r hi
  apply atRawIntroFrom (fold .erase) r
  intro gamma rho Xi a b i j upper lower left right hrho hf
  have hi' := renameInto hi rho Xi hrho
  rw [belowRawRename] at hi'
  exact commutationStep (r.relabel rho) a b i j upper lower left right hi' hf

theorem actualRawCommutation : OriginalTwoDeletionInternalTargets.RawCommutation := by
  intro body alpha Delta raw a b i j upper lower left right
  let A := fields (fold .erase) raw a b i j upper lower left right
  obtain ⟨h⟩ := atRawApply (fold .erase) raw a b i j upper lower left right
    (allRawCommutation (body := body) (Delta := A :: Delta) raw)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalProof
