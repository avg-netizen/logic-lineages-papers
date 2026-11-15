module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.BoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof


theorem noMemberAt (n : Nat) (seed param frontier child seedRank childRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hc : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) childRank child param))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hb := BoundProof.rankBound n body alpha Delta (suc seedRank) seed param frontier child seedRank childRank hr hf hm hc
  have he := trans (InternalAdditionLawsProof.leftSuccessor seedRank childRank) (symm (addSucc seedRank childRank))
  have hb' := PrimaryUncoveredCount.OrderProof.transport (OrdinaryArithmetic.addTerm (suc seedRank) childRank) seedRank
    (OrdinaryArithmetic.addTerm seedRank (suc childRank)) seedRank ⟨he⟩ ⟨refl seedRank⟩ hb
  obtain ⟨hz⟩ := PrimaryFiniteDescent.ArithmeticProof.budgetZero seedRank (suc childRank) hb'
  exact ⟨sucNeZeroApply hz⟩

theorem noMember (n : Nat) (seed param frontier child seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child))) :
    Nonempty (Derivation body Delta ⊥) := by
  apply programCases (OriginalDecodedRank.rank n) (Fin.cons child (Fin.cons param Fin.elim0)) _
  intro beta j Theta childRank hj hc
  simp only [consTermRename,emptyRename] at hc
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hrj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hfj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact noMemberAt n (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j)
    (seedRank.relabel j) childRank hrj hfj hmj hc
theorem nonemptyAt (n : Nat) (seed param frontier head tail seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hn : Nonempty (Derivation body Delta (eqn frontier z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail frontier))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hc := reconstructNonzero frontier head tail hn hh ht
  have he : Nonempty (Derivation body Delta (equal head head)) := by
    rw [equalEqn]
    exact ⟨InternalTagArithmeticSupportProof.refl head⟩
  exact noMember n seed param frontier head seedRank hr hf (containsHit frontier head tail head hc he)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionSupportProof
