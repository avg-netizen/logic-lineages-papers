module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalRawVariableRankTransportBindingProof OriginalRawVariableRankTransportSyntaxProof
open OriginalRawVariableRankUnaryProof
open OriginalRawSyntaxTransportInternalParametersQueryProof
open OriginalRawSyntaxTransportInternalFoldLambdaProof OriginalRawSyntaxTransportInternalFoldConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorBoundsProof

theorem lambdaTransformShape (erasing : Bool) (raw transformed d k domain child childOut : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) childOut d (suc k) child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw))) :
    Nonempty (Derivation body Delta (graph2 lambdaConstructor transformed domain childOut)) := by
  cases erasing <;> exact lambdaForward _ raw transformed d k domain child childOut hc hchild ht

theorem lambdaTransportAt (erasing : Bool) (raw transformed before after d k domain child childOut : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (hchild : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) childOut d (suc k) child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hf := lambdaFields raw k domain child hc
  have hl := unaryChildStrict raw child (andLeft hf) (andLeft (andRight hf))
  have hshape := lambdaTransformShape erasing raw transformed d k domain child childOut hc hchild ht
  exact belowRawApply (fold (transformMode erasing)) erasing raw child d (suc k) childOut before after hi hl hchild
    (rankLambdaForward raw before domain child hc hb)
    (rankLambdaForward transformed after domain childOut hshape ha)

theorem lambdaTransport (erasing : Bool) (raw transformed before after d k domain child : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (hc : Nonempty (Derivation body Delta (graph2 lambdaConstructor raw domain child)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply ternaryCases (fold (transformMode erasing)) d (suc k) child _
  intro beta j Theta childOut hj hchild
  rw [rankRelationRename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have ht' := renameInto ht j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [belowRawRename] at hi'
  rw [graph2Rename] at hc'
  rw [graph3Rename] at ht'
  rw [graph1Rename] at hb' ha'
  simp only [sucRelabel] at hchild
  exact lambdaTransportAt erasing (raw.relabel j) (transformed.relabel j) (before.relabel j) (after.relabel j)
    (d.relabel j) (k.relabel j) (domain.relabel j) (child.relabel j) childOut hi' hc' hchild ht' hb' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLambdaProof
