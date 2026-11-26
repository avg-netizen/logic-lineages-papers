module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero associativity)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalHereditaryAgendaPotentialAppendSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (front suffix joined branching a b : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z front suffix joined branching a b))) :
 Nonempty (Derivation body Delta (result joined branching a b)) := by
 have hfront := lengthZeroRecover front (InternalApplicationStepPeelSupportProof.andLeft hf)
 have happ := headTransport InternalApplicationValidityStackAppend.append joined front z (Fin.cons suffix Fin.elim0)
   hfront (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 obtain ⟨hjoined⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover joined suffix happ
 have ha0 := headTransport OriginalHereditaryAgendaPotential.agenda a front z (Fin.cons branching Fin.elim0)
   hfront (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)))
 obtain ⟨ha⟩ := valueUnique OriginalHereditaryAgendaPotential.agenda a z (Fin.cons z (Fin.cons branching Fin.elim0))
   ha0 (OriginalHereditaryAgendaPotentialRecurrenceProof.nilValue branching)
 have hb := headTransport OriginalHereditaryAgendaPotential.agenda b suffix joined (Fin.cons branching Fin.elim0)
   ⟨symm hjoined⟩ (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)))
 exact outputTransport OriginalHereditaryAgendaPotential.agenda b (add a b)
   (Fin.cons joined (Fin.cons branching Fin.elim0))
   ⟨symm (trans (InternalMultiplicationLawsProof.congAddRight b ha) (leftZero b))⟩ hb

theorem consCore (count front suffix joined branching a b head tail tailJoined headValue tailValue : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) front suffix joined branching a b)))
 (hc : Nonempty (Derivation body Delta (consGraph front head tail)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count tail)))
 (happ : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailJoined tail suffix)))
 (hh : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.frameCost headValue head branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda tailValue tail branching))) :
 Nonempty (Derivation body Delta (result joined branching a b)) := by
 have hiTail := rowApply count tail suffix tailJoined branching tailValue b hi
   (InternalApplicationStepPeelSupportProof.andIntro hl (InternalApplicationStepPeelSupportProof.andIntro happ (InternalApplicationStepPeelSupportProof.andIntro ht (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))))))
 have hj := InternalApplicationValidityStackAppendListProof.consForward front head tail suffix tailJoined joined
   hc happ (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 have hvalue := OriginalHereditaryAgendaPotentialRecurrenceProof.consValue joined head tailJoined branching headValue
   (add tailValue b) hj hh hiTail
 obtain ⟨he⟩ := OriginalHereditaryAgendaPotentialRecurrenceProof.consEquation front head tail branching headValue tailValue a
   hc hh ht (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)))
 exact outputTransport OriginalHereditaryAgendaPotential.agenda (add headValue (add tailValue b)) (add a b)
   (Fin.cons joined (Fin.cons branching Fin.elim0))
   ⟨trans (symm (associativity headValue tailValue b))
     (InternalMultiplicationLawsProof.congAddRight b (symm he))⟩ hvalue
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendCoreProof
