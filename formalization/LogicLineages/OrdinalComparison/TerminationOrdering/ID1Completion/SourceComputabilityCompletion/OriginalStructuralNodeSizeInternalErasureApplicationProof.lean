module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalAdditionLawsProof (add)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalRawSyntaxTransport
open OriginalStructuralNodeSizeInternalErasureDefinitions OriginalStructuralNodeSizeInternalErasureBindingProof
open OriginalStructuralNodeSizeInternalErasureSyntaxProof OriginalStructuralNodeSizeInternalErasureSupportProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorBoundsProof
open OriginalRawSyntaxTransportInternalCancellationNumberedProof (tupleSixRename)
open OriginalRawSyntaxTransportInternalFoldApplicationProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem applicationValues (input erased d k before after metadata first second firstOut secondOut firstCount secondCount firstAfter secondAfter : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor input metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    (he0 : Nonempty (Derivation body Delta (graph3 eraseRaw firstOut d k first)))
    (he1 : Nonempty (Derivation body Delta (graph3 eraseRaw secondOut d k second)))
    (hb0 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstCount first)))
    (hb1 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondCount second)))
    (ha0 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstAfter firstOut)))
    (ha1 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondAfter secondOut)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  have hs := applicationFields input metadata first second hc
  have hout := applicationForward .erase input erased d k metadata first second firstOut secondOut hc he0 he1 (andLeft hf)
  have ht := applicationFields erased metadata firstOut secondOut hout
  have hlt := binaryChildrenStrict input first second (andLeft hs) (andLeft (andRight hs)) (andRight (andRight hs))
  have hn0 := OriginalStructuralNodeSizeInternalErasureSupportProof.childCount input first d k firstOut firstCount firstAfter hi (andLeft hlt) he0 hb0 ha0
  have hn1 := OriginalStructuralNodeSizeInternalErasureSupportProof.childCount input second d k secondOut secondCount secondAfter hi (andRight hlt) he1 hb1 ha1
  have hb := OriginalStructuralNodeSizeInternalRecurrenceProof.binary input first second firstCount secondCount (andLeft hs) (andLeft (andRight hs)) (andRight (andRight hs)) hb0 hb1
  have ha := OriginalStructuralNodeSizeInternalRecurrenceProof.binary erased firstOut secondOut firstCount secondCount (andLeft ht) (andLeft (andRight ht)) (andRight (andRight ht)) hn0 hn1
  exact sharedCount input erased before after (suc (add firstCount secondCount)) (andLeft (andRight hf)) (andRight (andRight hf)) hb ha

theorem applicationCounts (input erased d k before after metadata first second firstOut secondOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor input metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    (he0 : Nonempty (Derivation body Delta (graph3 eraseRaw firstOut d k first)))
    (he1 : Nonempty (Derivation body Delta (graph3 eraseRaw secondOut d k second)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  apply countCases ![first,second,firstOut,secondOut] _
  intro beta rho Theta ys hrho hn
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have he0' := renameInto he0 rho Theta hrho
  have he1' := renameInto he1 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  simp only [graph3Rename,sucRelabel] at he0' he1'
  exact applicationValues (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) (firstOut.relabel rho) (secondOut.relabel rho) (ys 0) (ys 1) (ys 2) (ys 3) hi' hc' hf' he0' he1' (hn 0) (hn 1) (hn 2) (hn 3)

theorem applicationInvariant (input erased d k before after metadata first second : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph3 applicationConstructor input metadata first second)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  apply binaryChildCases (fold .erase) d k first second _
  intro beta rho Theta firstOut secondOut hrho he0 he1
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph3Rename] at hc'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  exact applicationCounts (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) (metadata.relabel rho) (first.relabel rho) (second.relabel rho) firstOut secondOut hi' hc' hf' he0 he1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureApplicationProof
