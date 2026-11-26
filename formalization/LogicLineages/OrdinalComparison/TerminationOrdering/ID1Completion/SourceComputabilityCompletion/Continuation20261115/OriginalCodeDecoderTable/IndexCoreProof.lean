module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.LengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open Continuation20261115.OriginalCodeDecoderTable Continuation20261115.OriginalCodeDecoderTable.IndexSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open InternalOriginalPairingOrderArithmeticProof (weakCases)
open InternalOriginalOrderSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem previousCell (n : Nat) (count oldTable previous singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row n count)))
    (hp : Nonempty (Derivation body Delta (graph2 (nextRow n) previous count oldTable)))
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc count) previous)))
    (hb : Nonempty (Derivation body Delta (Below cutoff (suc count))))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff output))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value oldTable cutoff)) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons cutoff (Fin.cons previous Fin.elim0)) _
  intro beta j Theta oldValue hj hk
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hk
  have hl' := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  simp only [lengthRename,sucRelabel] at hl'
  have hb' := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
  simp only [Below,orderRename,sucRelabel] at hb'
  have ha' := InternalGraphCompositionFunctionalityProof.renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hv' := InternalGraphCompositionFunctionalityProof.renameInto hv j Theta hj
  rw [graph2Rename] at hv'
  have hnew := OriginalHereditaryDeletionRowsPrefixLookupProof.prefixLookup
    (suc (count.relabel j)) (previous.relabel j) (cutoff.relabel j) (singleton.relabel j)
    (output.relabel j) oldValue hl' hb' ha' hk
  have he := valueUnique InternalRawListRecursion.lookup oldValue (value.relabel j)
    (Fin.cons (cutoff.relabel j) (Fin.cons (output.relabel j) Fin.elim0)) hnew hv'
  have hactual := outputTransport InternalRawListRecursion.lookup oldValue (value.relabel j)
    (Fin.cons (cutoff.relabel j) (Fin.cons (previous.relabel j) Fin.elim0)) he hk
  have hp' := InternalGraphCompositionFunctionalityProof.renameInto hp j Theta hj
  rw [graph2Rename] at hp'
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [rowRename] at hr'
  exact rowApply n (count.relabel j) (oldTable.relabel j)
    (previous.relabel j) (cutoff.relabel j) (value.relabel j) hr'
    (andIntro hb' (andIntro hp' hactual))

theorem successorAtValues (n : Nat)
    (count oldTable previous mark singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row n count)))
    (hp : Nonempty (Derivation body Delta (graph2 (nextRow n) previous count oldTable)))
    (hm : Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) mark oldTable (suc count))))
    (hc : Nonempty (Derivation body Delta (consGraph singleton mark z)))
    (hf : Nonempty (Derivation body Delta (fields n (suc count) oldTable output cutoff value))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value oldTable cutoff)) := by
  have hl := LengthProof.rowLength n count oldTable previous hp
  have ha := SupportProof.appendRecover n count previous oldTable mark singleton output
    hp (andLeft (andRight hf)) hm hc
  apply weakCases cutoff (suc count) _ (andLeft hf)
  · let A := Below cutoff (suc count)
    exact previousCell n count oldTable previous singleton output cutoff value
      (withHyp hr A) (withHyp hp A) (withHyp hl A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A)
      (withHyp (andRight (andRight hf)) A)
  · let A := eqn cutoff (suc count)
    have hlookup := OriginalHereditaryDeletionRowsEndProof.appendSingletonEnd (suc count) previous mark singleton output hl hc ha
    have hgiven := headTransport InternalRawListRecursion.lookup value cutoff (suc count)
      (Fin.cons output Fin.elim0)
      (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp (andRight (andRight hf)) A)
    have he := valueUnique InternalRawListRecursion.lookup mark value
      (Fin.cons (suc count) (Fin.cons output Fin.elim0)) (withHyp hlookup A) hgiven
    have hv := outputTransport (OriginalCodeDecoderStep.step n) mark value
      (Fin.cons oldTable (Fin.cons (suc count) Fin.elim0)) he (withHyp hm A)
    exact InternalApplicationValidityStackAppendRunProof.rightTransport
      (OriginalCodeDecoderStep.step n) value oldTable (suc count) cutoff
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ hv

theorem succCore (n : Nat) (count oldTable output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row n count)))
    (hf : Nonempty (Derivation body Delta (fields n (suc count) oldTable output cutoff value))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value oldTable cutoff)) := by
  apply SupportProof.rowCases n count oldTable _
  intro beta j Theta previous mark singleton hj hp hm hc
  rw [graph2Rename]
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  exact successorAtValues n (count.relabel j) (oldTable.relabel j)
    previous mark singleton (output.relabel j) (cutoff.relabel j) (value.relabel j) hr' hp hm hc hf'

theorem zeroCore (n : Nat) (oldTable output cutoff value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields n z oldTable output cutoff value))) :
    Nonempty (Derivation body Delta (graph2 (OriginalCodeDecoderStep.step n) value oldTable cutoff)) := by
  apply weakCases cutoff z _ (andLeft hf)
  · obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero
      (body := body) (Gamma := Below cutoff z :: Delta) cutoff
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn
      (Derivation.hypothesis List.mem_cons_self))⟩
  · let A := eqn cutoff z
    apply InternalAcceptanceSupportProof.programCases (OriginalCodeDecoderStep.step n)
      (Fin.cons oldTable (Fin.cons z Fin.elim0)) _
    intro beta j Theta mark hj hm
    rw [graph2Rename]
    simp only [consTermRename,emptyRename,zRelabel] at hm
    have hf' := InternalGraphCompositionFunctionalityProof.renameInto (withHyp hf A) j Theta hj
    simp only [fieldsRename,zRelabel] at hf'
    have heq : Nonempty (Derivation body Theta (eqn (cutoff.relabel j) z)) := by
      simpa only [A,InternalSliceInductionSyntaxProof.eqnRename,zRelabel] using
        (Nonempty.intro (Derivation.hypothesis (hj A List.mem_cons_self)))
    have hc := SupportProof.baseRecover n (oldTable.relabel j) mark (output.relabel j)
      hm (andLeft (andRight hf'))
    have hl := OriginalAllPositionContextDeleteBaseProof.lookupZero (output.relabel j) mark z hc
    have hgiven := headTransport InternalRawListRecursion.lookup (value.relabel j) (cutoff.relabel j) z
      (Fin.cons (output.relabel j) Fin.elim0) heq (andRight (andRight hf'))
    have he := valueUnique InternalRawListRecursion.lookup mark (value.relabel j)
      (Fin.cons z (Fin.cons (output.relabel j) Fin.elim0)) hl hgiven
    have hv := outputTransport (OriginalCodeDecoderStep.step n) mark (value.relabel j)
      (Fin.cons (oldTable.relabel j) (Fin.cons z Fin.elim0)) he hm
    obtain ⟨heq⟩ := heq
    exact InternalApplicationValidityStackAppendRunProof.rightTransport (OriginalCodeDecoderStep.step n)
      (value.relabel j) (oldTable.relabel j) z (cutoff.relabel j) ⟨symm heq⟩ hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.IndexCoreProof
