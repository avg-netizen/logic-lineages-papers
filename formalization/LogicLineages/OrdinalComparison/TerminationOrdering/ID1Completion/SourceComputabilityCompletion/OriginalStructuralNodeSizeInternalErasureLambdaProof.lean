module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLambdaProof
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
open OriginalRawSyntaxTransportInternalFoldLambdaProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem lambdaValues (input erased d k before after metadata child childOut childCount childAfter : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor input metadata child)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    (he0 : Nonempty (Derivation body Delta (graph3 eraseRaw childOut d (suc k) child)))
    (hb0 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw childCount child)))
    (ha0 : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw childAfter childOut)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  have hs := lambdaFields input k metadata child hc
  have hout := lambdaForward .erase input erased d k metadata child childOut hc he0 (andLeft hf)
  have ht := lambdaFields erased k metadata childOut hout
  have hlt := unaryChildStrict input child (andLeft hs) (andLeft (andRight hs))
  have hn0 := OriginalStructuralNodeSizeInternalErasureSupportProof.childCount input child d (suc k) childOut childCount childAfter hi hlt he0 hb0 ha0
  have hb := OriginalStructuralNodeSizeInternalRecurrenceProof.unary input child childCount (andLeft hs) (andLeft (andRight hs)) hb0
  have ha := OriginalStructuralNodeSizeInternalRecurrenceProof.unary erased childOut childCount (andLeft ht) (andLeft (andRight ht)) hn0
  exact sharedCount input erased before after (suc childCount) (andLeft (andRight hf)) (andRight (andRight hf)) hb ha

theorem lambdaCounts (input erased d k before after metadata child childOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor input metadata child)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    (he0 : Nonempty (Derivation body Delta (graph3 eraseRaw childOut d (suc k) child)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  apply countCases ![child,childOut] _
  intro beta rho Theta ys hrho hn
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  have he0' := renameInto he0 rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  simp only [graph3Rename,sucRelabel] at he0'
  exact lambdaValues (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) (metadata.relabel rho) (child.relabel rho) (childOut.relabel rho) (ys 0) (ys 1) hi' hc' hf' he0' (hn 0) (hn 1)

theorem lambdaInvariant (input erased d k before after metadata child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor input metadata child)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after)))
    : Nonempty (Derivation body Delta (equal before after)) := by
  apply ternaryCases (fold .erase) d (suc k) child _
  intro beta rho Theta childOut hrho he0
  rw [equalRename]
  have hi' := renameInto hi rho Theta hrho
  have hc' := renameInto hc rho Theta hrho
  have hf' := renameInto hf rho Theta hrho
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
  simp only [sucRelabel] at he0
  exact lambdaCounts (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) (metadata.relabel rho) (child.relabel rho) childOut hi' hc' hf' he0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLambdaProof
