module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementNilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedAgreement WeightedAgreementSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel zRelabel)
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreementSyntaxProof

theorem nonzero (weight : Program 1) (left right ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls left)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw weight left)))
    (hn : Nonempty (Derivation body Delta (eqn left z).not)) :
    Nonempty (Derivation body Delta (eqn ls rs)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (WeightedAgreementQueriesProof.queries weight) ![left,right] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![left,right] i).relabel j) = ![left.relabel j,right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  have haj := renameInto ha j Theta hj
  have hlj := renameInto hl j Theta hj
  have hrj := renameInto hr j Theta hj
  have ihj := renameInto ih j Theta hj
  have hnj := renameInto hn j Theta hj
  rw [agreementRename] at haj
  rw [graph1Rename] at hlj hrj
  rw [belowRawRename] at ihj
  simp only [notRename,eqnRelabel,zRelabel] at hnj
  obtain ⟨hc,hv,hp,ht,hs,hw⟩ := WeightedAgreementQueriesProof.recover weight
    (left.relabel j) (right.relabel j) ys hnj hq
  exact WeightedAgreementConsAtProof.cons weight (left.relabel j) (ys 0) (ys 1) (right.relabel j)
    (ys 2) (ys 3) (ys 4) (ls.relabel j) (rs.relabel j) (ys 5) (ys 6) (ys 7)
    hc haj hv hp hlj hrj ht hw hs ihj

theorem atRaw (weight : Program 1) (left right ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls left)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw weight left))) :
    Nonempty (Derivation body Delta (eqn ls rs)) := by
  apply formulaCases (eqn left z)
  · have he : Nonempty (Derivation body ((eqn left z) :: Delta) (eqn left z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he'⟩ := he
    obtain ⟨ha'⟩ := withHyp ha (eqn left z)
    have d := Derivation.equalityElimination
      (agreement (.var (.inr 0)) (right.relabel Sum.inl))
      (InternalTagArithmeticSyntaxProof.emb left) (InternalTagArithmeticSyntaxProof.emb z) he'
    simp only [instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,agreementSubst,
      InternalTagArithmeticSyntaxProof.liftBind,InternalTagArithmeticSyntaxProof.varBind] at d
    have hl0 := headTransport (Fold.weighted weight) ls left z Fin.elim0 he (withHyp hl _)
    exact WeightedAgreementNilProof.nil weight right ls rs ⟨d ha'⟩ hl0 (withHyp hr _)
  · exact nonzero weight left right ls rs (withHyp ha _) (withHyp hl _) (withHyp hr _) (withHyp ih _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementCoreProof
