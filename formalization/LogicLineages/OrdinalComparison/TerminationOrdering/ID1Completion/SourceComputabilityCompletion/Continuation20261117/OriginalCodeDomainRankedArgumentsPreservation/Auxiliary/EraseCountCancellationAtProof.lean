module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.CountRemoveAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseCountCancellationAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.BoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans symm addSucc addZero congSuc cancelSuc)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open Continuation20261114
open Continuation20261115.OriginalArgumentPermutationClosure
open CountAgreement CountAgreementBindingProof

theorem atCounts (left head tail right rest needle tc rc whole : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode left head tail)))
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (he : Nonempty (Derivation body Delta (EraseInvariant.countEffect right head rest (suc z))))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count tc tail needle)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc rest needle)))
    (hw : Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count whole right needle))) :
    Nonempty (Derivation body Delta (eqn tc rc)) := by
  apply formulaCases (eqn head needle)
  · have hsame : Nonempty (Derivation body ((eqn head needle) :: Delta) (eqn head needle)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl := ArgumentEntryCount.InternalProof.internalEqualCons body alpha _ left head tail needle tc
      (withHyp hc _) (withHyp ht _) hsame
    obtain ⟨hmatch⟩ := agreementApply left right needle (suc tc) whole (withHyp ha _) hl (withHyp hw _)
    obtain ⟨hremove⟩ := CountEffectBindingProof.equalQuery right head rest (suc z) needle whole rc
      (withHyp he _) (withHyp hw _) (withHyp hr _) hsame
    have hadd : Derivation body ((eqn head needle) :: Delta)
        (eqn (OrdinaryArithmetic.addTerm rc (suc z)) (suc rc)) :=
      trans (addSucc rc z) (congSuc (addZero rc))
    exact ⟨cancelSuc (trans hmatch (trans hremove hadd))⟩
  · have hdiff : Nonempty (Derivation body ((eqn head needle).not :: Delta) (eqn head needle).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl := ArgumentEntryCount.InternalProof.internalUnequalCons body alpha _ left head tail needle tc
      (withHyp hc _) (withHyp ht _) hdiff
    obtain ⟨hmatch⟩ := agreementApply left right needle tc whole (withHyp ha _) hl (withHyp hw _)
    obtain ⟨hremove⟩ := CountEffectBindingProof.unequalQuery right head rest (suc z) needle whole rc
      (withHyp he _) (withHyp hw _) (withHyp hr _) hdiff
    exact ⟨trans hmatch hremove⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseCountCancellationAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseCountCancellationAtProof
