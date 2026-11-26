module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.GrowthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.StepProof
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

open InternalOriginalOrderSyntaxProof
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem growthDrop (pool before after beforeCount afterCount : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included before after)))
    (hb : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count beforeCount pool before)))
    (ha : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count afterCount pool after)))
    (hg : Nonempty (Derivation body Delta (PrimaryStability.growthWitness pool before after))) :
    Nonempty (Derivation body Delta (ltF afterCount beforeCount)) := by
  obtain ⟨hg⟩ := hg
  let candidate : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := graph2 contains (suc z) (pool.relabel Sum.inl) candidate ⊓
    ((graph2 contains (suc z) (before.relabel Sum.inl) candidate).not ⊓
      graph2 contains (suc z) (after.relabel Sum.inl) candidate)
  let Theta := A :: Delta.map weaken
  have hj : ∀ q ∈ Delta, q.relabel Sum.inl ∈ Theta :=
    fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have hi' := renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [includedRename] at hi'
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [graph2Rename] at hb'
  have ha' := renameInto ha (Sum.inl : alpha → alpha ⊕ Fin 1) Theta hj
  rw [graph2Rename] at ha'
  have h : Derivation body Theta A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hd⟩ := PrimaryUncoveredCount.CompareProof.internalStrictDecrease body (alpha ⊕ Fin 1) Theta
    (pool.relabel Sum.inl) (before.relabel Sum.inl) (after.relabel Sum.inl)
    (beforeCount.relabel Sum.inl) (afterCount.relabel Sum.inl) candidate hi' hb' ha'
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  have hd' : Derivation body Theta ((ltF afterCount beforeCount).relabel Sum.inl) := by
    simpa only [orderRename] using hd
  exact ⟨Derivation.existentialElimination hg hd'⟩

theorem stepAlternative : Targets.StepAlternative := by
  intro E body alpha Delta pool before after parameter beforeCount afterCount he hb ha
  let A := PrimaryMonotonicity.included after before
  apply formulaCases A
  · exact ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  · have hg := PrimaryStability.GrowthProof.internalGrowthWitness E body alpha (A.not :: Delta)
      pool before after parameter (withHyp he A.not) ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hi := PrimaryStability.InclusionProof.expansionIncluded E pool before after parameter (withHyp he A.not)
    obtain ⟨hd⟩ := growthDrop pool before after beforeCount afterCount hi (withHyp hb A.not) (withHyp ha A.not) hg
    exact ⟨orRight hd⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.StepProof
