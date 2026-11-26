module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalListCodecDecompositionSupportProof
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof

theorem nonempty2 (seed param frontier head tail : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    (htail : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail frontier)))
    : Nonempty (Derivation body Delta ⊥) := by
  exact ExhaustionSupportProof.nonemptyAt seed param frontier head tail hf hn hhead htail

theorem nonempty1 (seed param frontier head : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    : Nonempty (Derivation body Delta ⊥) := by
  apply programCases InternalListCodec.tailCode (Fin.cons frontier Fin.elim0) _
  intro beta j Theta tail hj hx
  simp only [consTermRename,emptyRename] at hx
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn frontier z).relabel j).not) at hnj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hheadj := renameInto hhead j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hheadj
  exact nonempty2 (seed.relabel j) (param.relabel j) (frontier.relabel j) (head.relabel j) tail hfj hnj hheadj hx

theorem nonempty0 (seed param frontier : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    : Nonempty (Derivation body Delta ⊥) := by
  apply programCases InternalListCodec.headCode (Fin.cons frontier Fin.elim0) _
  intro beta j Theta head hj hx
  simp only [consTermRename,emptyRename] at hx
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn frontier z).relabel j).not) at hnj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  exact nonempty1 (seed.relabel j) (param.relabel j) (frontier.relabel j) head hfj hnj hx

theorem outputZero (seed param frontier : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param))) :
    Nonempty (Derivation body Delta (eqn frontier z)) := by
  let A := eqn frontier z
  apply formulaCases A
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · obtain ⟨bad⟩ := nonempty0 seed param frontier (withHyp hf A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.explosion bad⟩

theorem exhaustion : Targets.InternalRankExhaustion := by
  intro body alpha Delta seed param
  apply programCases (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency)
    (Fin.cons (suc seed) (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta frontier hj hf
  simp only [graph3Rename,zRelabel,sucRelabel]
  simp only [consTermRename,emptyRename,sucRelabel] at hf
  exact outputTransport (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier z
    (Fin.cons (suc (seed.relabel j)) (Fin.cons (seed.relabel j) (Fin.cons (param.relabel j) Fin.elim0)))
    (outputZero (seed.relabel j) (param.relabel j) frontier hf) hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionProof
