module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open GrowthSyntaxProof PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem witnessIntro (pool before after candidate : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 contains (suc z) pool candidate)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (suc z) before candidate).not))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) after candidate))) :
    Nonempty (Derivation body Delta (growthWitness pool before after)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hn⟩ := hn
  obtain ⟨hm⟩ := hm
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb candidate)
  rw [witnessInstance]
  exact Derivation.conjunctionIntroduction hp (Derivation.conjunctionIntroduction hn hm)

theorem poolFromNew (E : Program 3) (pool before after parameter candidate : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) after pool before parameter)))
    (hn : Nonempty (Derivation body Delta (graph2 contains (suc z) before candidate).not))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) after candidate))) :
    Nonempty (Derivation body Delta (graph2 contains (suc z) pool candidate)) := by
  obtain ⟨hd⟩ := PrimaryExpansionSoundness.Proof.expansionSoundness E pool before parameter after candidate he hm
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination hd
    (Derivation.implicationIntroduction (Derivation.explosion (Derivation.implicationElimination
      (addHyp hn _) (Derivation.hypothesis List.mem_cons_self))))
    (Derivation.implicationIntroduction (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)))⟩

theorem includedIfNoGrowth (E : Program 3) (pool before after parameter : OTerm alpha)
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) after pool before parameter)))
    (hn : Nonempty (Derivation body Delta (growthWitness pool before after).not)) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included after before)) := by
  apply introduce after before
  intro beta j Theta candidate hj hm
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hn' := renameInto hn j Theta hj
  change Nonempty (Derivation body Theta ((growthWitness pool before after).relabel j).not) at hn'
  rw [witnessRename] at hn'
  let A := graph2 contains (suc z) (before.relabel j) candidate
  have hnot : Nonempty (Derivation body (A.not :: Theta) A.not) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp := poolFromNew E (pool.relabel j) (before.relabel j) (after.relabel j)
    (parameter.relabel j) candidate (withHyp he' A.not) hnot (withHyp hm A.not)
  obtain ⟨hw⟩ := witnessIntro (pool.relabel j) (before.relabel j) (after.relabel j) candidate
    hp hnot (withHyp hm A.not)
  obtain ⟨hn'⟩ := withHyp hn' A.not
  exact ⟨Derivation.classical (Derivation.implicationElimination hn' hw)⟩

theorem internalGrowthWitness : Targets.InternalGrowthWitness := by
  intro E body alpha Delta pool before after parameter he hn
  let W := growthWitness pool before after
  obtain ⟨hi⟩ := includedIfNoGrowth E pool before after parameter (withHyp he W.not)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hn⟩ := withHyp hn W.not
  exact ⟨Derivation.classical (Derivation.implicationElimination hn hi)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthProof
