module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedHelpersProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureFuelProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add leftZero congAddLeft)
open InternalListCodecSupportProof (consGraph)
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalHereditaryAgendaPotentialTaggedSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (jobs tagged branching total : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (fields z jobs tagged branching total))) :
 Nonempty (Derivation body Delta (result tagged branching total)) := by
 have hj := lengthZeroRecover jobs (InternalApplicationStepPeelSupportProof.andLeft hf)
 have hs0 := headTransport OriginalHereditaryBudgetSum.sum total jobs z (Fin.cons branching Fin.elim0) hj (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))
 obtain ⟨he⟩ := valueUnique OriginalHereditaryBudgetSum.sum total z (Fin.cons z (Fin.cons branching Fin.elim0))
   hs0 (OriginalHereditaryBudgetSumRecurrenceProof.nilValue branching)
 have ht0 := headTransport OriginalHereditaryVisitScheduler.tagVisits tagged jobs z Fin.elim0 hj (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 obtain ⟨ht⟩ := valueUnique OriginalHereditaryVisitScheduler.tagVisits tagged z (Fin.cons z Fin.elim0)
   ht0 OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagNil
 have ha := headTransport OriginalHereditaryAgendaPotential.agenda z z tagged (Fin.cons branching Fin.elim0)
   ⟨symm ht⟩ (OriginalHereditaryAgendaPotentialRecurrenceProof.nilValue branching)
 have hz : Derivation body Delta (eqn (add total total) z) :=
   trans (congAddLeft total he) (trans (InternalMultiplicationLawsProof.congAddRight z he) (leftZero z))
 exact outputTransport OriginalHereditaryAgendaPotential.agenda z (add total total)
   (Fin.cons tagged (Fin.cons branching Fin.elim0)) ⟨symm hz⟩ ha

theorem consCore (count jobs tagged branching total head tail visit taggedTail headValue tailValue : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count)))
 (hf : Nonempty (Derivation body Delta (fields (suc count) jobs tagged branching total)))
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count tail)))
 (hvisit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z head)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits taggedTail tail)))
 (hh : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.jobBudget headValue head branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum tailValue tail branching))) :
 Nonempty (Derivation body Delta (result tagged branching total)) := by
 have htail := rowApply count tail taggedTail branching tailValue hi (InternalApplicationStepPeelSupportProof.andIntro hl (InternalApplicationStepPeelSupportProof.andIntro htag ht))
 have hcons := OriginalHereditaryAgendaPotentialTaggedHelpersProof.tagCons jobs head tail tagged visit taggedTail
   hc hvisit htag (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf))
 have hcost := OriginalHereditaryAgendaPotentialFrameProof.visitCost visit head branching headValue hvisit hh
 have hout := OriginalHereditaryAgendaPotentialRecurrenceProof.consValue tagged visit taggedTail branching
   (add headValue headValue) (add tailValue tailValue) hcons hcost htail
 obtain ⟨he⟩ := OriginalHereditaryBudgetSumRecurrenceProof.consEquation jobs head tail branching headValue tailValue total
   hc hh ht (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf))
 have heq : Derivation body Delta
   (eqn (add (add headValue headValue) (add tailValue tailValue)) (add total total)) :=
   trans (InternalApplicationCertifiedResultFoldClosureFuelProof.interchange headValue headValue tailValue tailValue)
     (trans (congAddLeft (add headValue tailValue) (symm he))
       (InternalMultiplicationLawsProof.congAddRight total (symm he)))
 exact outputTransport OriginalHereditaryAgendaPotential.agenda _ (add total total)
   (Fin.cons tagged (Fin.cons branching Fin.elim0)) ⟨heq⟩ hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedCoreProof
