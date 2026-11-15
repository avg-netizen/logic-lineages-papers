module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionProof
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

theorem nonempty2 (n : Nat) (seed param frontier head tail seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    (htail : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail frontier)))
    : Nonempty (Derivation body Delta ⊥) := by
  exact ExhaustionSupportProof.nonemptyAt n seed param frontier head tail seedRank hr hf hn hhead htail

theorem nonempty1 (n : Nat) (seed param frontier head seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    (hhead : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    : Nonempty (Derivation body Delta ⊥) := by
  apply programCases InternalListCodec.tailCode (Fin.cons frontier Fin.elim0) _
  intro beta j Theta tail hj hx
  simp only [consTermRename,emptyRename] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn frontier z).relabel j).not) at hnj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  have hheadj := renameInto hhead j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hheadj
  exact nonempty2 n (seed.relabel j) (param.relabel j) (frontier.relabel j) (head.relabel j) tail (seedRank.relabel j) hrj hfj hnj hheadj hx

theorem nonempty0 (n : Nat) (seed param frontier seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param)))
    (hn : Nonempty (Derivation body Delta ((eqn frontier z).not)))
    : Nonempty (Derivation body Delta ⊥) := by
  apply programCases InternalListCodec.headCode (Fin.cons frontier Fin.elim0) _
  intro beta j Theta head hj hx
  simp only [consTermRename,emptyRename] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hfj := renameInto hf j Theta hj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hfj
  have hnj := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((eqn frontier z).relabel j).not) at hnj
  simp only [graph1Rename,graph3Rename,eqnRelabel,sucRelabel,zRelabel] at hnj
  exact nonempty1 n (seed.relabel j) (param.relabel j) (frontier.relabel j) head (seedRank.relabel j) hrj hfj hnj hx

theorem outputZero (n : Nat) (seed param frontier seedRank : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (OriginalDecodedRank.rank n) seedRank seed param)))
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier (suc seedRank) seed param))) :
    Nonempty (Derivation body Delta (eqn frontier z)) := by
  let A := eqn frontier z
  apply formulaCases A
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · obtain ⟨bad⟩ := nonempty0 n seed param frontier seedRank (withHyp hr A.not) (withHyp hf A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.explosion bad⟩

theorem exhaustion : Targets.InternalRankExhaustion := by
  intro n body alpha Delta seed param seedRank hr
  apply programCases (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n))
    (Fin.cons (suc seedRank) (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta frontier hj hf
  simp only [graph3Rename,zRelabel,sucRelabel]
  simp only [consTermRename,emptyRename,sucRelabel] at hf
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  exact outputTransport (ExchangeFrontier.bindList (OriginalDecodedDependencies.dependencies n)) frontier z
    (Fin.cons (suc (seedRank.relabel j)) (Fin.cons (seed.relabel j) (Fin.cons (param.relabel j) Fin.elim0)))
    (outputZero n (seed.relabel j) (param.relabel j) frontier (seedRank.relabel j) hrj hf) hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedFrontierRank.ExhaustionProof
