module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureProof
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

open OriginalStructuralNodeSizeInternalErasureTagsProof OriginalStructuralNodeSizeInternalErasureBindingProof
open OriginalStructuralNodeSizeInternalErasureIntroductionProof OriginalStructuralNodeSizeInternalErasureLeafProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
theorem unaryInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply orCases (arityOneTags input ha)
  · intro Theta inc ht
    exact lambdaTagInvariant input erased d k before after (weakenProof hi inc) ht (weakenProof hf inc)
  · intro Theta inc ht
    exact ordinaryTagInvariant input erased d k before after (weakenProof hi inc) ht (weakenProof hf inc)

theorem binaryInvariant (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply orCases (arityTwoTags input ha)
  · intro Theta inc ht
    exact applicationTagInvariant input erased d k before after (weakenProof hi inc) ht (weakenProof hf inc)
  · intro Theta inc ht
    apply orCases ht
    · intro Xi inc2 ht2
      exact numberedTagInvariant input erased d k before after (weakenProof (weakenProof hi inc) inc2) ht2 (weakenProof (weakenProof hf inc) inc2)
    · intro Xi inc2 ht2
      exact consTagInvariant input erased d k before after (weakenProof (weakenProof hi inc) inc2) ht2 (weakenProof (weakenProof hf inc) inc2)

theorem invarianceStep (input erased d k before after : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw input)))
    (hf : Nonempty (Derivation body Delta (fields input d k erased before after))) :
    Nonempty (Derivation body Delta (equal before after)) := by
  apply arityCases input
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
    exact leafInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) ha (andLeft hf') (andLeft (andRight hf')) (andRight (andRight hf'))
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hi' := renameInto hi rho Theta hrho
    rw [belowRawRename] at hi'
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
    exact unaryInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) hi' ha hf'
  · intro beta rho Theta hrho ha
    rw [equalRename]
    have hi' := renameInto hi rho Theta hrho
    rw [belowRawRename] at hi'
    have hf' := renameInto hf rho Theta hrho
    simp only [fields,conjunctionRename,graph1Rename,graph3Rename] at hf'
    exact binaryInvariant (input.relabel rho) (erased.relabel rho) (d.relabel rho) (k.relabel rho) (before.relabel rho) (after.relabel rho) hi' ha hf'

theorem allRawInvariant (input : OTerm alpha) : Nonempty (Derivation body Delta (AtRaw input)) := by
  apply rawInduction input
  intro beta Theta r hi
  apply atRawIntroFrom r
  intro gamma rho Xi d k erased before after hrho hf
  have hi' := renameInto hi rho Xi hrho
  rw [belowRawRename] at hi'
  exact invarianceStep (r.relabel rho) erased d k before after hi' hf

theorem actualInternalErasureInvariant : OriginalStructuralNodeSizeTargets.InternalErasureInvariant := by
  intro body alpha Delta input erased typ cutoff before after
  let A := fields input typ cutoff erased before after
  obtain ⟨h⟩ := atRawApply input typ cutoff erased before after
    (allRawInvariant (body := body) (Delta := A :: Delta) input)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalErasureProof
