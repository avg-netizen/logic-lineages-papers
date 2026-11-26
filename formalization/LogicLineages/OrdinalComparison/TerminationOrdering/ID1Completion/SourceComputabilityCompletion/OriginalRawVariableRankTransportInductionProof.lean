module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportInductionProof
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
open OriginalRawVariableRankTransportIntroductionProof
open OriginalRawVariableRankTransportLeafProof OriginalRawVariableRankTransportTagsProof
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)

theorem unaryTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (harity : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply orCases (arityOneTags raw harity)
  · intro Theta inc htag
    exact lambdaTagTransport erasing raw transformed before after d k
      (weakenProof hi inc) htag (weakenProof ht inc) (weakenProof hb inc) (weakenProof ha inc)
  · intro Theta inc htag
    exact ordinaryTagTransport erasing raw transformed before after d k
      (weakenProof hi inc) htag (weakenProof ht inc) (weakenProof hb inc) (weakenProof ha inc)

theorem binaryTransport (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (harity : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply orCases (arityTwoTags raw harity)
  · intro Theta inc htag
    exact applicationTagTransport erasing raw transformed before after d k
      (weakenProof hi inc) htag (weakenProof ht inc) (weakenProof hb inc) (weakenProof ha inc)
  · intro Theta inc htag
    apply orCases htag
    · intro Xi inc' hn
      exact numberedTagTransport erasing raw transformed before after d k
        (weakenProof (weakenProof hi inc) inc') hn (weakenProof (weakenProof ht inc) inc')
        (weakenProof (weakenProof hb inc) inc') (weakenProof (weakenProof ha inc) inc')
    · intro Xi inc' hn
      exact consTagTransport erasing raw transformed before after d k
        (weakenProof (weakenProof hi inc) inc') hn (weakenProof (weakenProof ht inc) inc')
        (weakenProof (weakenProof hb inc) inc') (weakenProof (weakenProof ha inc) inc')

theorem transportStep (erasing : Bool) (raw transformed before after d k : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (BelowRaw (fold (transformMode erasing)) erasing raw)))
    (ht : Nonempty (Derivation body Delta (graph3 (fold (transformMode erasing)) transformed d k raw)))
    (hb : Nonempty (Derivation body Delta (graph1 variableRankRaw before raw)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankRaw after transformed))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  apply arityCases raw
  · intro beta j Theta hj harity
    rw [rankRelationRename]
    have ht' := renameInto ht j Theta hj
    have hb' := renameInto hb j Theta hj
    have ha' := renameInto ha j Theta hj
    rw [graph3Rename] at ht'
    rw [graph1Rename] at hb' ha'
    exact leafTransport erasing (raw.relabel j) (transformed.relabel j)
      (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j) harity ht' hb' ha'
  · intro beta j Theta hj harity
    rw [rankRelationRename]
    have hi' := renameInto hi j Theta hj
    have ht' := renameInto ht j Theta hj
    have hb' := renameInto hb j Theta hj
    have ha' := renameInto ha j Theta hj
    rw [belowRawRename] at hi'
    rw [graph3Rename] at ht'
    rw [graph1Rename] at hb' ha'
    exact unaryTransport erasing (raw.relabel j) (transformed.relabel j)
      (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j) hi' harity ht' hb' ha'
  · intro beta j Theta hj harity
    rw [rankRelationRename]
    have hi' := renameInto hi j Theta hj
    have ht' := renameInto ht j Theta hj
    have hb' := renameInto hb j Theta hj
    have ha' := renameInto ha j Theta hj
    rw [belowRawRename] at hi'
    rw [graph3Rename] at ht'
    rw [graph1Rename] at hb' ha'
    exact binaryTransport erasing (raw.relabel j) (transformed.relabel j)
      (before.relabel j) (after.relabel j) (d.relabel j) (k.relabel j) hi' harity ht' hb' ha'

/-- Strong induction is entirely in ordinary arithmetic. No source decoding,
standard-model truth or generic native machine execution enters the proof. -/
theorem allRawTransport (erasing : Bool) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw (fold (transformMode erasing)) erasing raw)) := by
  apply rawInduction (fold (transformMode erasing)) erasing raw
  intro beta Theta r hi
  apply atRawIntroFrom (fold (transformMode erasing)) erasing r
  intro gamma j Xi d k transformed before after hj ht hb ha
  have hi' := renameInto hi j Xi hj
  rw [belowRawRename] at hi'
  exact transportStep erasing (r.relabel j) transformed before after d k hi' ht hb ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportInductionProof
