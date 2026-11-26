module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsEndProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedIndexedCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryInternalAnnotatedScanDefinitions
open OriginalHereditaryAnnotatedExpansion (scan)
open OriginalHereditaryInternalAnnotatedScanIndexedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open InternalOriginalPairingOrderArithmeticProof (weakCases)
open InternalOriginalOrderSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem previousCell (count role typ raw jobs previous singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hp : Nonempty (Derivation body Delta (graph5 scan previous count role typ raw jobs)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count previous)))
    (hb : Nonempty (Derivation body Delta (Below cutoff count)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff output))) :
    Nonempty (Derivation body Delta (graph5 cell value cutoff role typ raw jobs)) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons cutoff (Fin.cons previous Fin.elim0)) _
  intro beta j Theta oldValue hj hk
  rw [graph5Rename]
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
  rw [graph5Rename] at hp'
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  exact rowApply (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j)
    (previous.relabel j) (cutoff.relabel j) (value.relabel j) hr'
    (andIntro hb' (andIntro hp' hactual))

theorem successorAtValues 
    (count role typ raw jobs previous mark singleton output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hp : Nonempty (Derivation body Delta (graph5 scan previous count role typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton mark z)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) role typ raw jobs output cutoff value))) :
    Nonempty (Derivation body Delta (graph5 cell value cutoff role typ raw jobs)) := by
  have hl := SixSol20261113.Runtime.SourceFramedScanLengthProof.scanLength count role typ raw jobs previous hp
  have ha := SixSol20261113.Runtime.SourceFramedScanQueries.scanAppendRecover count previous role typ raw jobs mark singleton output
    hp (andLeft (andRight hf)) hm hc
  apply weakCases cutoff count _ (andLeft hf)
  · let A := Below cutoff count
    exact previousCell count role typ raw jobs previous singleton output cutoff value
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
    have hv := outputTransport cell mark value
      (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))) he (withHyp hm A)
    exact headTransport cell value count cutoff
      (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ hv

theorem succCore (count role typ raw jobs output cutoff value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields (suc count) role typ raw jobs output cutoff value))) :
    Nonempty (Derivation body Delta (graph5 cell value cutoff role typ raw jobs)) := by
  apply SixSol20261113.Runtime.SourceFramedScanQueries.scanCases count role typ raw jobs _
  intro beta j Theta previous mark singleton hj hp hm hc
  rw [graph5Rename]
  have hr' := renameInto hr j Theta hj
  rw [rowRename] at hr'
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  exact successorAtValues (count.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j)
    previous mark singleton (output.relabel j) (cutoff.relabel j) (value.relabel j) hr' hp hm hc hf'

theorem zeroCore (role typ raw jobs output cutoff value : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields z role typ raw jobs output cutoff value))) :
    Nonempty (Derivation body Delta (graph5 cell value cutoff role typ raw jobs)) := by
  obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body := body) (Gamma := Delta) cutoff
  obtain ⟨hl⟩ := andLeft hf
  exact ⟨Derivation.explosion (Derivation.implicationElimination hn hl)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedIndexedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedIndexedCoreProof
