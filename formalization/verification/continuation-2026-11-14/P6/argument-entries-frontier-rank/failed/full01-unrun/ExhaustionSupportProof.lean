module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.BoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionSupportProof
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

theorem noMemberAt (seed param frontier child previous : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child)))
    (hp : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) previous seed seed param))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hw := ExchangeFrontierWitness.Proof.successorWitness body alpha Delta ArgumentEntriesFrontier.dependency
    seed seed param previous frontier child hp hf hm
  apply PrimaryExpansionSoundness.WitnessProof.casesWitness (ExchangeFrontierWitness.dependencyEdge ArgumentEntriesFrontier.dependency)
    previous child param _ hw
  intro beta j Theta node hj hmem hedge
  have hpj := renameInto hp j Theta hj
  rw [graph3Rename] at hpj
  have hb := BoundProof.rankBound body beta Theta (seed.relabel j) (seed.relabel j) (param.relabel j) (previous.relabel j) node hpj hmem
  obtain ⟨hz⟩ := PrimaryFiniteDescent.ArithmeticProof.budgetZero (seed.relabel j) node hb
  obtain ⟨hlt⟩ := CoreProof.edgeDescent node (child.relabel j) (param.relabel j) hedge
  have hlt0 := InternalSquareRootArithmeticSupportProof.orderRight (child.relabel j) hz hlt
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body beta (child.relabel j)
  exact ⟨Derivation.implicationElimination (weakenClosed hn Theta) hlt0⟩

theorem noMember (seed param frontier child : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier child))) :
    Nonempty (Derivation body Delta ⊥) := by
  apply programCases (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency)
    (Fin.cons seed (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta previous hj hp
  simp only [consTermRename,emptyRename] at hp
  have hfj := renameInto hf j Theta hj
  simp only [graph3Rename,sucRelabel] at hfj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  exact noMemberAt (seed.relabel j) (param.relabel j) (frontier.relabel j) (child.relabel j) previous hfj hmj hp

theorem nonemptyAt (seed param frontier head tail : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList ArgumentEntriesFrontier.dependency) frontier (suc seed) seed param)))
    (hn : Nonempty (Derivation body Delta (eqn frontier z).not))
    (hh : Nonempty (Derivation body Delta (graph1 InternalListCodec.headCode head frontier)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail frontier))) :
    Nonempty (Derivation body Delta ⊥) := by
  have hc := reconstructNonzero frontier head tail hn hh ht
  have he : Nonempty (Derivation body Delta (equal head head)) := by
    rw [equalEqn]
    exact ⟨InternalTagArithmeticSupportProof.refl head⟩
  exact noMember seed param frontier head hf (containsHit frontier head tail head hc he)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontierRank.ExhaustionSupportProof
