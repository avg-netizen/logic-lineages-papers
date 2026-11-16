module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountHeadQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountAgreementNilProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof (refl symm sucNeZeroApply)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open Continuation20261114
open Continuation20261115.OriginalArgumentPermutationClosure
open CountAgreement CountAgreementSyntaxProof CountAgreementBindingProof

theorem rightZero (right : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement z right))) :
    Nonempty (Derivation body Delta (eqn right z)) := by
  apply formulaCases (eqn right z)
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · let Theta := (eqn right z).not :: Delta
    have hn : Nonempty (Derivation body Theta (eqn right z).not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ha' := withHyp ha (eqn right z).not
    apply OriginalLambdaConstructorGraphSyntaxProof.queryCases CountHeadQueriesProof.queries ![right] _
    intro beta j ys Omega hj hq
    have hx : (fun i => (![right] i).relabel j) = ![right.relabel j] := by
      funext i; fin_cases i; rfl
    rw [hx] at hq
    have hnj := renameInto hn j Omega hj
    have haj := renameInto ha' j Omega hj
    simp only [notRename,eqnRelabel,zRelabel] at hnj
    simp only [agreementRename,zRelabel] at haj
    obtain ⟨hc,ht⟩ := CountHeadQueriesProof.recover (right.relabel j) ys hnj hq
    have hr := ArgumentEntryCount.InternalProof.internalEqualCons body beta Omega
      (right.relabel j) (ys 0) (ys 1) (ys 0) (ys 2) hc ht ⟨refl (ys 0)⟩
    obtain ⟨hbad⟩ := agreementApply z (right.relabel j) (ys 0) z (suc (ys 2)) haj
      (ArgumentEntryCount.InternalProof.internalNil body beta Omega (ys 0)) hr
    exact ⟨Derivation.explosion (sucNeZeroApply (symm hbad))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountAgreementNilProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.CountAgreementNilProof
