module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.ConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
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

open ConsProof
theorem consCore (n : Nat) (arity : Fin n → Nat)
    (raw head tail symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hf : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  have hstep := InternalRawListRecursionProof.consForward (OriginalRawSyntaxTransport.constant 2 0)
    (OriginalSourceHeads.filterStep n arity) raw head tail out ![symbols,types] hc hf
  apply InternalRawListRecursionProof.stepCases (OriginalRawSyntaxTransport.constant 2 0)
    (OriginalSourceHeads.filterStep n arity) out head tail ![symbols,types] _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hw' := renameInto hw j Theta hj
  rw [graph3Rename] at hw'
  have hparams : (fun i => (![symbols,types] i).relabel j) =
      Fin.cons (symbols.relabel j) (Fin.cons (types.relabel j) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hparams] at hr hs
  have hr' : Nonempty (Derivation body Theta
      (graph3 (OriginalSourceHeads.filterHeads n arity) rest (tail.relabel j)
        (symbols.relabel j) (types.relabel j))) := by
    simpa only [graph3,programGraph,OriginalSourceHeads.filterHeads,InternalRawListRecursion.recGraph] using hr
  exact consAt n arity (raw.relabel j) (head.relabel j) (tail.relabel j) (symbols.relabel j)
    (needle.relabel j) (types.relabel j) (out.relabel j) rest (value.relabel j) hb' hc' hr' hw' hs

theorem nonzeroAt (n : Nat) (arity : Fin n → Nat) (raw head symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hf : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  apply programCases InternalListCodec.tailCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta tail hj ht
  rw [resultRename]
  simp only [consTermRename,emptyRename] at ht
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  have hh' := renameInto hh j Theta hj
  rw [graph1Rename] at hh'
  have hw' := renameInto hw j Theta hj
  rw [graph3Rename] at hw'
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact consCore n arity (raw.relabel j) (head.relabel j) tail (symbols.relabel j) (needle.relabel j)
    (types.relabel j) (out.relabel j) (value.relabel j) hb'
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) hw' hf'

theorem nonzeroCore (n : Nat) (arity : Fin n → Nat) (raw symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hf : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  apply programCases InternalListCodec.headCode (Fin.cons raw Fin.elim0) _
  intro beta j Theta head hj hh
  rw [resultRename]
  simp only [consTermRename,emptyRename] at hh
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hn' := renameInto hn j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hn'
  have hw' := renameInto hw j Theta hj
  rw [graph3Rename] at hw'
  have hf' := renameInto hf j Theta hj
  rw [graph3Rename] at hf'
  exact nonzeroAt n arity (raw.relabel j) head (symbols.relabel j) (needle.relabel j)
    (types.relabel j) (out.relabel j) (value.relabel j) hb' hn' hh hw' hf'

theorem zeroMemberFalse (raw needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hz := headTransport contains (numeral 1) raw z (Fin.cons needle Fin.elim0) he hm
  obtain ⟨hbad⟩ := valueUnique contains (numeral 1) z ![z,needle] hz (containsNil needle)
  exact ⟨sucNeZeroApply hbad⟩

theorem core (n : Nat) (arity : Fin n → Nat) (raw symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw)))
    (hw : Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) value needle symbols types)))
    (hf : Nonempty (Derivation body Delta (graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf0 := headTransport (OriginalSourceHeads.filterHeads n arity) out raw z ![symbols,types] hz (withHyp hf A)
    have hnil := OriginalSourceHeads.InternalProof.internalFilterNil n arity body alpha (A :: Delta) symbols types
    have ho := valueUnique (OriginalSourceHeads.filterHeads n arity) out z ![z,symbols,types] hf0 hnil
    apply andIntro
    · let M := graph2 contains (numeral 1) out needle
      obtain ⟨bad⟩ := zeroMemberFalse out needle (withHyp ho M) ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩
    · let Q := qualifies raw needle value
      have hq : Nonempty (Derivation body (Q :: A :: Delta) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨bad⟩ := zeroMemberFalse raw needle (withHyp hz Q) (andLeft hq)
      exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩
  · exact nonzeroCore n arity raw symbols needle types out value (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw A.not) (withHyp hf A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
