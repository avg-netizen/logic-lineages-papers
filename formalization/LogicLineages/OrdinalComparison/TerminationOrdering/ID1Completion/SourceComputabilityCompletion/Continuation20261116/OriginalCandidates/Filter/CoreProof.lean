module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.ConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.CoreProof
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

open StepSupportProof LogicProof

open ConsProof
theorem consCore (H : Program 1)
    (raw head tail symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols)))
    (hf : Nonempty (Derivation body Delta (graph2 (filterCandidates H) out raw symbols))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  have hstep := InternalRawListRecursionProof.consForward (OriginalRawSyntaxTransport.constant 1 0)
    (filterStep H) raw head tail out ![symbols] hc hf
  apply InternalRawListRecursionProof.stepCases (OriginalRawSyntaxTransport.constant 1 0)
    (filterStep H) out head tail ![symbols] _ hstep
  intro beta j Theta rest hj hr hs
  rw [resultRename]
  have hb' := renameInto hb j Theta hj
  rw [belowRawRename] at hb'
  have hc' := renameInto hc j Theta hj
  rw [graph2Rename] at hc'
  have hw' := renameInto hw j Theta hj
  rw [graph2Rename] at hw'
  have hparams : (fun i => (![symbols] i).relabel j) =
      Fin.cons (symbols.relabel j) Fin.elim0 := by
    funext i
    exact Fin.cases rfl (fun k => Fin.elim0 k) i
  rw [hparams] at hr hs
  have hr' : Nonempty (Derivation body Theta
      (graph2 (filterCandidates H) rest (tail.relabel j)
        (symbols.relabel j))) := by
    simpa only [graph2,programGraph,filterCandidates,InternalRawListRecursion.recGraph] using hr
  exact consAt H (raw.relabel j) (head.relabel j) (tail.relabel j) (symbols.relabel j)
    (needle.relabel j) (types.relabel j) (out.relabel j) rest (value.relabel j) hb' hc' hr' hw' hs

theorem nonzeroAt (H : Program 1) (raw head symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head raw)))
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols)))
    (hf : Nonempty (Derivation body Delta (graph2 (filterCandidates H) out raw symbols))) :
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
  rw [graph2Rename] at hw'
  have hf' := renameInto hf j Theta hj
  rw [graph2Rename] at hf'
  exact consCore H (raw.relabel j) (head.relabel j) tail (symbols.relabel j) (needle.relabel j)
    (types.relabel j) (out.relabel j) (value.relabel j) hb'
    (reconstructNonzero (raw.relabel j) (head.relabel j) tail hn' hh' ht) hw' hf'

theorem nonzeroCore (H : Program 1) (raw symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not))
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols)))
    (hf : Nonempty (Derivation body Delta (graph2 (filterCandidates H) out raw symbols))) :
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
  rw [graph2Rename] at hw'
  have hf' := renameInto hf j Theta hj
  rw [graph2Rename] at hf'
  exact nonzeroAt H (raw.relabel j) head (symbols.relabel j) (needle.relabel j)
    (types.relabel j) (out.relabel j) (value.relabel j) hb' hn' hh hw' hf'

theorem zeroMemberFalse (raw needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) raw needle))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hz := headTransport contains (numeral 1) raw z (Fin.cons needle Fin.elim0) he hm
  obtain ⟨hbad⟩ := valueUnique contains (numeral 1) z ![z,needle] hz (containsNil needle)
  exact ⟨sucNeZeroApply hbad⟩

theorem core (H : Program 1) (raw symbols needle types out value : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw)))
    (hw : Nonempty (Derivation body Delta (graph2 (OriginalTypedDecoder.packedCheck H) value needle symbols)))
    (hf : Nonempty (Derivation body Delta (graph2 (filterCandidates H) out raw symbols))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  let A := eqn raw z
  apply formulaCases A
  · have hz : Nonempty (Derivation body (A :: Delta) (eqn raw z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hf0 := headTransport (filterCandidates H) out raw z ![symbols] hz (withHyp hf A)
    have hnil : Nonempty (Derivation body (A :: Delta) (graph2 (filterCandidates H) z z symbols)) :=
      InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 1 0) (filterStep H) z ![symbols]
        (InternalAcceptanceConjunctionProof.constantZeroValue ![symbols])
    have ho := valueUnique (filterCandidates H) out z ![z,symbols] hf0 hnil
    apply andIntro
    · let M := graph2 contains (numeral 1) out needle
      obtain ⟨bad⟩ := zeroMemberFalse out needle (withHyp ho M) ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩
    · let Q := qualifies raw needle value
      have hq : Nonempty (Derivation body (Q :: A :: Delta) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨bad⟩ := zeroMemberFalse raw needle (withHyp hz Q) (andLeft hq)
      exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩
  · exact nonzeroCore H raw symbols needle types out value (withHyp hb A.not)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp hw A.not) (withHyp hf A.not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.CoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.CoreProof
