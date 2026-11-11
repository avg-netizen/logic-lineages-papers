module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm trans congSuc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open OriginalRawVariableRankTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalArithmeticProgramsSupportProof InternalAdditionLawsProof
open InternalOriginalPairingOrderArithmeticProof InternalOriginalOrderProof InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof

theorem relationOfEqual (erasing : Bool) (after before : OTerm alpha)
    (he : Nonempty (Derivation body Delta (equal after before))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  cases erasing with
  | false => exact he
  | true =>
    simp only [equalEqn] at he
    obtain ⟨he⟩ := he
    exact ⟨InternalQuotientComparisonProof.equalToNext he⟩

theorem relationTransport (erasing : Bool) (after before after' before' : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (equal after after')))
    (hb : Nonempty (Derivation body Delta (equal before before')))
    (hr : Nonempty (Derivation body Delta (RankRelation erasing after' before'))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  cases erasing with
  | false =>
    simp only [RankRelation,Bool.false_eq_true,if_false,equalEqn] at ha hb hr ⊢
    obtain ⟨ha⟩ := ha
    obtain ⟨hb⟩ := hb
    obtain ⟨hr⟩ := hr
    exact ⟨InternalTagArithmeticSupportProof.trans ha (InternalTagArithmeticSupportProof.trans hr (InternalTagArithmeticSupportProof.symm hb))⟩
  | true =>
    apply weakTransport after before after' before'
    · simpa only [equalEqn] using ha
    · simpa only [equalEqn] using hb
    · exact hr

theorem relationAddition (erasing : Bool) (after before afterFirst beforeFirst afterSecond beforeSecond : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition after afterFirst afterSecond)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition before beforeFirst beforeSecond)))
    (hf : Nonempty (Derivation body Delta (RankRelation erasing afterFirst beforeFirst)))
    (hs : Nonempty (Derivation body Delta (RankRelation erasing afterSecond beforeSecond))) :
    Nonempty (Derivation body Delta (RankRelation erasing after before)) := by
  have hea := valueUnique InternalArithmeticPrograms.addition after (add afterFirst afterSecond)
    (Fin.cons afterFirst (Fin.cons afterSecond Fin.elim0)) ha (additionValue afterFirst afterSecond)
  have heb := valueUnique InternalArithmeticPrograms.addition before (add beforeFirst beforeSecond)
    (Fin.cons beforeFirst (Fin.cons beforeSecond Fin.elim0)) hb (additionValue beforeFirst beforeSecond)
  apply relationTransport erasing after before (add afterFirst afterSecond) (add beforeFirst beforeSecond)
    (by simpa only [equalEqn] using hea) (by simpa only [equalEqn] using heb)
  cases erasing with
  | false =>
    simp only [RankRelation,Bool.false_eq_true,if_false,equalEqn] at hf hs ⊢
    obtain ⟨hf⟩ := hf
    obtain ⟨hs⟩ := hs
    exact ⟨InternalTagArithmeticSupportProof.trans (InternalMultiplicationLawsProof.congAddRight afterSecond hf)
      (InternalAdditionLawsProof.congAddLeft beforeFirst hs)⟩
  | true => exact addWeakBoth afterFirst beforeFirst afterSecond beforeSecond hf hs

theorem relationNonincrease (after before : OTerm alpha)
    (h : Nonempty (Derivation body Delta (RankRelation true after before))) :
    Nonempty (Derivation body Delta (RankNonincrease after before)) := by
  obtain ⟨hc⟩ := strictWeakConflict before after (⊥ : Formula alpha)
    (show Nonempty (Derivation body (InternalLessThan.strictLess before after :: Delta)
      (InternalLessThan.strictLess before after)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    (withHyp h _)
  exact ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTransportArithmeticProof
