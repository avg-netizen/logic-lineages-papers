module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open InternalOriginalOrderSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalStructuralNodeSizeInternalErasureDefinitions
open OriginalStructuralNodeSizeInternalErasureSyntaxProof
open OriginalStructuralNodeSizeInternalErasureLambdaProof OriginalStructuralNodeSizeInternalErasureOrdinaryProof
open OriginalStructuralNodeSizeInternalErasureApplicationProof OriginalStructuralNodeSizeInternalErasureConsProof
open OriginalStructuralNodeSizeInternalErasureNumberedProof
open OriginalRawSyntaxTransportInternalParserUnaryProof OriginalRawSyntaxTransportInternalParserBinaryProof
open OriginalRawSyntaxTransportInternalParserNumberedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaTagInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply lambdaCases input _ ht
  intro beta rho Theta domain child hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact lambdaInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) domain child hi' hc hf'

theorem ordinaryTagInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply ordinaryCases input _ ht
  intro beta rho Theta head child hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact ordinaryInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) head child hi' hc hf'

theorem applicationTagInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply applicationCases input _ ht
  intro beta rho Theta domain first second hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact applicationInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) domain first second hi' hc hf'

theorem consTagInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply consCases input _ ht
  intro beta rho Theta tau first second hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact consInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) tau first second hi' hc hf'

theorem numberedTagInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply numberedCases input _ ht
  intro beta rho Theta label head tau base types extras hrho hc
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact numberedInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) label head tau types base extras hi' hc hf'


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureTagsProof
