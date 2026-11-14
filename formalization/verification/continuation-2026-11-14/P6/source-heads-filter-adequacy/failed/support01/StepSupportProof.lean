module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.InductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
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

theorem stepZero (n : Nat) (arity : Fin n → Nat) (out head rest symbols types : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) z head symbols types)))
    (hs : Nonempty (Derivation body Delta (graph4 (OriginalSourceHeads.filterStep n arity) out head rest symbols types))) :
    Nonempty (Derivation body Delta (eqn out rest)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,symbols,types]
  have h := zeroBranchElim _ (.projection 1) (OriginalSourceHeads.consOf (.projection 0) (.projection 1)) out xs
    (OriginalSourceHeads.InternalProof.windowGraph n arity z head rest symbols types hw) hs
  exact valueUnique (.projection (1 : Fin 4)) out rest xs h (projectionValue 1 xs)

theorem stepNonzero (n : Nat) (arity : Fin n → Nat) (out head rest symbols types value : OTerm alpha)
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value head symbols types)))
    (hn : Nonempty (Derivation body Delta (eqn value z).not))
    (hs : Nonempty (Derivation body Delta (graph4 (OriginalSourceHeads.filterStep n arity) out head rest symbols types))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)) := by
  let xs : Fin 4 → OTerm alpha := ![head,rest,symbols,types]
  have h := nonzeroBranch _ (.projection 1) (OriginalSourceHeads.consOf (.projection 0) (.projection 1)) out value xs
    (OriginalSourceHeads.InternalProof.windowGraph n arity value head rest symbols types hw) hn hs
  exact binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1) out head rest xs h
    (projectionValue 0 xs) (projectionValue 1 xs)

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

theorem tailResult (n : Nat) (arity : Fin n → Nat) (raw head tail symbols needle types rest value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) rest tail symbols types)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types))) :
    Nonempty (Derivation body Delta (result tail symbols needle types rest value)) :=
  belowRawApply n arity raw tail symbols needle types rest value hb
    (consTailDescent raw head tail hc) (andIntro hr hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
