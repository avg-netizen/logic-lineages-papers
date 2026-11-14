module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.LogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.ConsProof
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

open StepSupportProof LogicProof

theorem queryEqual (n : Nat) (arity : Fin n → Nat) (head needle symbols types q value : OTerm alpha)
    (hq : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) q head symbols types)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (he : Nonempty (Derivation body Delta (equal head needle))) :
    Nonempty (Derivation body Delta (eqn q value)) := by
  rw [equalEqn] at he
  have h := headTransport (OriginalHeadWindow.window n arity) q head needle
    (Fin.cons symbols (Fin.cons types Fin.elim0)) he hq
  exact valueUnique (OriginalHeadWindow.window n arity) q value ![needle,symbols,types] h hw

theorem zeroTransfer (q value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn q value)))
    (hz : Nonempty (Derivation body Delta (eqn q z))) :
    Nonempty (Derivation body Delta (eqn value z)) := by
  obtain ⟨he⟩ := he; obtain ⟨hz⟩ := hz
  exact ⟨trans (symm he) hz⟩

theorem nonzeroTransfer (q value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn q value)))
    (hn : Nonempty (Derivation body Delta (eqn q z).not)) :
    Nonempty (Derivation body Delta (eqn value z).not) := by
  obtain ⟨he⟩ := withHyp he (eqn value z)
  obtain ⟨hn⟩ := withHyp hn (eqn value z)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn
    (trans he (Derivation.hypothesis List.mem_cons_self)))⟩

theorem consAtValue (n : Nat) (arity : Fin n → Nat)
    (raw head tail symbols needle types out rest value q : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) rest tail symbols types)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hs : Nonempty (Derivation body Delta (graph4 (OriginalSourceHeads.filterStep n arity) out head rest symbols types)))
    (hq : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) q head symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  have old := tailResult n arity raw head tail symbols needle types rest value hb hc hr hw
  let A := eqn q z
  let B := equal head needle
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn q z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hw0 := outputTransport (OriginalHeadWindow.window n arity) q z ![head,symbols,types] hz (withHyp hq A)
    have ho := stepZero n arity out head rest symbols types hw0 (withHyp hs A)
    apply formulaCases B
    · have he := queryEqual n arity head needle symbols types q value (withHyp (withHyp hq A) B)
        (withHyp (withHyp hw A) B) ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact zeroResult raw tail symbols needle types out rest value (withHyp ho B)
        (zeroTransfer q value he (withHyp hz B)) (withHyp (withHyp old A) B)
    · have hn : Nonempty (Derivation body (B.not :: A :: Delta) B.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have maps := memberEqual out rest needle (withHyp ho B.not)
      exact missResult raw head tail symbols needle types out rest value
        (withHyp (withHyp hc A) B.not) hn (withHyp (withHyp old A) B.not) maps.1 maps.2
  · have hnq : Nonempty (Derivation body (A.not :: Delta) (eqn q z).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := stepNonzero n arity out head rest symbols types q (withHyp hq A.not) hnq (withHyp hs A.not)
    apply formulaCases B
    · have he : Nonempty (Derivation body (B :: A.not :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hqv := queryEqual n arity head needle symbols types q value
        (withHyp (withHyp hq A.not) B) (withHyp (withHyp hw A.not) B) he
      have hn := nonzeroTransfer q value hqv (withHyp hnq B)
      exact trueResult raw symbols needle types out value
        (containsHit out head rest needle (withHyp ho B) he)
        (andIntro (containsHit raw head tail needle (withHyp (withHyp hc A.not) B) he) hn)
    · have hn : Nonempty (Derivation body (B.not :: A.not :: Delta) B.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have maps := memberMiss out head rest needle (withHyp ho B.not) hn
      exact missResult raw head tail symbols needle types out rest value
        (withHyp (withHyp hc A.not) B.not) hn (withHyp (withHyp old A.not) B.not) maps.1 maps.2

theorem consAt (n : Nat) (arity : Fin n → Nat)
    (raw head tail symbols needle types out rest value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hr : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) rest tail symbols types)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hs : Nonempty (Derivation body Delta (graph4 (OriginalSourceHeads.filterStep n arity) out head rest symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  apply programCases (OriginalHeadWindow.window n arity) (Fin.cons head (Fin.cons symbols (Fin.cons types Fin.elim0))) _
  intro beta j Theta q hj hq
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hq
  have hbj := renameInto hb j Theta hj
  simp only [belowRawRename,graph2Rename,graph3Rename,InternalApplicationStepPeelSupportProof.graph4Rename] at hbj
  have hcj := renameInto hc j Theta hj
  simp only [belowRawRename,graph2Rename,graph3Rename,InternalApplicationStepPeelSupportProof.graph4Rename] at hcj
  have hrj := renameInto hr j Theta hj
  simp only [belowRawRename,graph2Rename,graph3Rename,InternalApplicationStepPeelSupportProof.graph4Rename] at hrj
  have hwj := renameInto hw j Theta hj
  simp only [belowRawRename,graph2Rename,graph3Rename,InternalApplicationStepPeelSupportProof.graph4Rename] at hwj
  have hsj := renameInto hs j Theta hj
  simp only [belowRawRename,graph2Rename,graph3Rename,InternalApplicationStepPeelSupportProof.graph4Rename] at hsj
  exact consAtValue n arity (raw.relabel j) (head.relabel j) (tail.relabel j) (symbols.relabel j) (needle.relabel j) (types.relabel j) (out.relabel j) (rest.relabel j) (value.relabel j) q hbj hcj hrj hwj hsj hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.ConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.ConsProof
