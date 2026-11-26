module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTagsProof
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

theorem lambdaTagCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply lambdaCases raw _ ht
  intro beta rho Theta domain child hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  exact lambdaAt0 (raw.relabel rho) domain child (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' hc hf'

theorem ordinaryTagCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply ordinaryCases raw _ ht
  intro beta rho Theta head child hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  exact ordinaryAt0 (raw.relabel rho) head child (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' hc hf'

theorem applicationTagCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply applicationCases raw _ ht
  intro beta rho Theta domain first second hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  exact applicationAt0 (raw.relabel rho) domain first second (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' hc hf'

theorem consTagCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply consCases raw _ ht
  intro beta rho Theta tau first second hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  exact consAt0 (raw.relabel rho) tau first second (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' hc hf'

theorem numberedTagCommute (raw a b i j upper lower left right : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold .erase) raw)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (hf : Nonempty (Derivation body Delta (fields (fold .erase) raw a b i j upper lower left right))) :
    Nonempty (Derivation body Delta (equal left right)) := by
  apply numberedCases raw _ ht
  intro beta rho Theta label head tau base types extras hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,InternalLessThan.strictLess,orderRename,graph3Rename,sucRelabel] at hf'
  exact numberedAt0 (raw.relabel rho) label head tau types base extras (a.relabel rho) (b.relabel rho) (i.relabel rho) (j.relabel rho) (upper.relabel rho) (lower.relabel rho) (left.relabel rho) (right.relabel rho) hi' hc hf'


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalTagsProof
