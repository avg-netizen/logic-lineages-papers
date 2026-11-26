module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCountCancellationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseSearchCompletenessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel)
open InternalTagArithmeticSupportProof (refl sucNeZeroApply)
open InternalApplicationStepPeelSupportProof (andLeft)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open Continuation20261114
open Continuation20261115.OriginalArgumentPermutationClosure
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof

theorem atCount (left head tail right acc bit rest tc : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc right head)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail head))) :
    Nonempty (Derivation body Delta (eqn bit (suc z))) := by
  have hb := andLeft (EraseInvariantProof.actualResult right head acc bit rest hv hp)
  have hleft := ArgumentEntryCount.InternalProof.internalEqualCons body alpha Delta left head tail head tc hc ht ⟨refl head⟩
  have habsent := EraseAbsenceProof.actualResult right head acc bit rest hv hp
  apply OriginalTypedDecoderInternalBranchProof.orCases hb
  · have hz : Nonempty (Derivation body ((eqn bit z) :: Delta) (eqn bit z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hzero := EraseAbsenceResultProof.bitTransport right head bit z hz (withHyp habsent _)
    obtain ⟨hbad⟩ := agreementApply left right head (suc tc) z (withHyp ha _) (withHyp hleft _)
      (EraseAbsenceResultProof.zeroCount right head hzero)
    exact ⟨Derivation.explosion (sucNeZeroApply hbad)⟩
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem found (left head tail right acc bit rest : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc right head)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (eqn bit (suc z))) := by
  apply InternalAcceptanceSupportProof.programCases ArgumentEntryCount.count ![tail,head] _
  intro beta j Theta tc hj ht
  have hx : (fun i => (![tail,head] i).relabel j) = ![tail.relabel j,head.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ht
  simp only [eqnRelabel,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel]
  have hcj := renameInto hc j Theta hj
  have haj := renameInto ha j Theta hj
  have hvj := renameInto hv j Theta hj
  have hpj := renameInto hp j Theta hj
  rw [graph2Rename] at hcj hvj hpj
  rw [agreementRename] at haj
  exact atCount (left.relabel j) (head.relabel j) (tail.relabel j) (right.relabel j)
    (acc.relabel j) (bit.relabel j) (rest.relabel j) tc hcj haj hvj hpj ht
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseSearchCompletenessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseSearchCompletenessProof
