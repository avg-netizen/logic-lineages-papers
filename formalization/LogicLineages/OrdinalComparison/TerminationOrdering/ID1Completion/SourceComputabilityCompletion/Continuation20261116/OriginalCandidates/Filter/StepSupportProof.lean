module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.StepSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Induction InductionSyntaxProof InductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nonzeroBranch {m : Nat} (control a b : Program m) (out value : OTerm alpha)
    (xs : Fin m → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph control value xs)))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (hs : Nonempty (Derivation body Delta (programGraph (InternalAcceptance.branch control a b) out xs))) :
    Nonempty (Derivation body Delta (programGraph b out xs)) := by
  apply zeroSuccessorCases Delta value _
  · obtain ⟨hn⟩ := withHyp hn (eqn value z)
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta pred hj he
    simp only [InternalControlGraphSupportProof.programRename]
    have hcj := renameInto hc j Theta hj
    have hsj := renameInto hs j Theta hj
    simp only [InternalControlGraphSupportProof.programRename] at hcj hsj
    exact successorBranchElim control a b (out.relabel j) pred
      (fun i => (xs i).relabel j) (outputTransport control (value.relabel j) (suc pred) _ he hcj) hsj

theorem controlValue (H : Program 1) (value head rest gamma : OTerm alpha)
    (hq : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value head gamma))) :
    Nonempty (Derivation body Delta (graph3
      (.composition (OriginalTypedDecoder.packedCheck H) ![.projection 0,.projection 2]) value head rest gamma)) :=
  binaryValue (OriginalTypedDecoder.packedCheck H) (.projection 0) (.projection 2) value head gamma
    ![head,rest,gamma] hq (projectionValue 0 ![head,rest,gamma]) (projectionValue 2 ![head,rest,gamma])

theorem stepZero (H : Program 1) (out head rest symbols types : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) z head symbols)))
    (hs : Nonempty (Derivation body Delta (graph3 (filterStep H) out head rest symbols))) :
    Nonempty (Derivation body Delta (eqn out rest)) := by
  have h := zeroBranchElim _ (.projection 1) (consOf (.projection 0) (.projection 1)) out ![head,rest,symbols]
    (controlValue H z head rest symbols hw) hs
  exact valueUnique (.projection 1) out rest ![head,rest,symbols] h (projectionValue 1 ![head,rest,symbols])

theorem stepNonzero (H : Program 1) (out head rest symbols types value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value head symbols)))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (hs : Nonempty (Derivation body Delta (graph3 (filterStep H) out head rest symbols))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)) := by
  have h := nonzeroBranch _ (.projection 1) (consOf (.projection 0) (.projection 1)) out value ![head,rest,symbols]
    (controlValue H value head rest symbols hw) hn hs
  exact binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) out head rest ![head,rest,symbols] h
    (projectionValue 0 ![head,rest,symbols]) (projectionValue 1 ![head,rest,symbols])

theorem forward (raw symbols needle types out value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (result raw symbols needle types out value)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle))) :
    Nonempty (Derivation body Delta (qualifies raw needle value)) := by
  obtain ⟨hi⟩ := hi; obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) hm⟩
theorem backward (raw symbols needle types out value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (result raw symbols needle types out value)))
    (hq : Nonempty (Derivation body Delta (qualifies raw needle value))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)) := by
  obtain ⟨hi⟩ := hi; obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) hq⟩

theorem tailResult (H : Program 1) (raw head tail symbols needle types rest value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph2 (filterCandidates H) rest tail symbols)))
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols))) :
    Nonempty (Derivation body Delta (result tail symbols needle types rest value)) :=
  belowRawApply H raw tail symbols needle types rest value hb
    (consTailDescent raw head tail hc) (andIntro hr hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.StepSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.StepSupportProof
