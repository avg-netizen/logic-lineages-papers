module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedCoreProof
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
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsIndexedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open InternalOriginalPairingOrderArithmeticProof (weakCases)
open InternalOriginalOrderSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem previousCell (Q : Program 2) (count input parameter previous singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row Q count)))
    (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous count input parameter)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count previous)))
    (hb : Nonempty (Derivation body Delta (Below cutoff count)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff output))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons cutoff (Fin.cons previous Fin.elim0)) _
  intro beta j Theta oldValue hj hk
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hk
  have hl' := renameInto hl j Theta hj
  rw [lengthRename] at hl'
  have hb' := renameInto hb j Theta hj
  simp only [Below,orderRename] at hb'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hv' := renameInto hv j Theta hj
  rw [graph2Rename] at hv'
  have hnew := OriginalHereditaryDeletionRowsPrefixLookupProof.prefixLookup
    (count.relabel j) (previous.relabel j) (cutoff.relabel j) (singleton.relabel j)
    (output.relabel j) oldValue hl' hb' ha' hk
  have he := valueUnique InternalRawListRecursion.lookup oldValue (value.relabel j)
    (Fin.cons (cutoff.relabel j) (Fin.cons (output.relabel j) Fin.elim0)) hnew hv'
  have hactual := outputTransport InternalRawListRecursion.lookup oldValue (value.relabel j)
    (Fin.cons (cutoff.relabel j) (Fin.cons (previous.relabel j) Fin.elim0)) he hk
  have hp' := renameInto hp j Theta hj
  rw [graph3Rename] at hp'
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  exact rowApply Q (count.relabel j) (input.relabel j) (parameter.relabel j)
    (previous.relabel j) (cutoff.relabel j) (value.relabel j) hr'
    (andIntro hb' (andIntro hp' hactual))

theorem successorAtValues (Q : Program 2)
    (count input parameter previous mark singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row Q count)))
    (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous count input parameter)))
    (hm : Nonempty (Derivation body Delta (graph3 (observation Q) mark count input parameter)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton mark z)))
    (hf : Nonempty (Derivation body Delta (fields Q (suc count) input parameter output cutoff value))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  have hl := OriginalHereditaryDeletionRowsScanLengthProof.scanLength Q count input parameter previous hp
  have ha := OriginalHereditaryDeletionRowsStepProof.scanAppendRecover Q count previous input parameter mark singleton output
    hp (andLeft (andRight hf)) hm hc
  apply weakCases cutoff count _ (andLeft hf)
  · let A := Below cutoff count
    exact previousCell Q count input parameter previous singleton output cutoff value
      (withHyp hr A) (withHyp hp A) (withHyp hl A)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp ha A)
      (withHyp (andRight (andRight hf)) A)
  · let A := eqn cutoff count
    have hlookup := OriginalHereditaryDeletionRowsEndProof.appendSingletonEnd count previous mark singleton output hl hc ha
    have hgiven := headTransport InternalRawListRecursion.lookup value cutoff count
      (Fin.cons output Fin.elim0)
      (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (withHyp (andRight (andRight hf)) A)
    have he := valueUnique InternalRawListRecursion.lookup mark value
      (Fin.cons count (Fin.cons output Fin.elim0)) (withHyp hlookup A) hgiven
    have hv := outputTransport (observation Q) mark value
      (Fin.cons count (Fin.cons input (Fin.cons parameter Fin.elim0))) he (withHyp hm A)
    exact headTransport (observation Q) value count cutoff
      (Fin.cons input (Fin.cons parameter Fin.elim0))
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ hv

theorem succCore (Q : Program 2) (count input parameter output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row Q count)))
    (hf : Nonempty (Derivation body Delta (fields Q (suc count) input parameter output cutoff value))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  apply OriginalHereditaryDeletionRowsCasesProof.scanCases Q count input parameter _
  intro beta j Theta previous mark singleton hj hp hm hc
  rw [graph3Rename]
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  exact successorAtValues Q (count.relabel j) (input.relabel j) (parameter.relabel j)
    previous mark singleton (output.relabel j) (cutoff.relabel j) (value.relabel j) hr' hp hm hc hf'

theorem zeroCore (Q : Program 2) (input parameter output cutoff value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields Q z input parameter output cutoff value))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body := body) (Gamma := Delta) cutoff
  obtain ⟨hl⟩ := andLeft hf
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hl)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedCoreProof
