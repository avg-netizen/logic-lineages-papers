module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundBindingProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus (Derivation Formula instantiate weaken)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph
open InternalApplicationCertificateConstructors
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open InternalStrongInduction InternalStrongInductionProof InternalStrongInductionSyntaxProof
open NumberedWindowInternalThinUncoveredCountBoundDefinitions.Bound NumberedWindowInternalThinUncoveredCountBoundSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalThinUncoveredCountOrderProof
open NumberedWindowInternalSparseScratchMembership (scratchMember)
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atRawIntro  (raw : OTerm alpha)
    (h : Nonempty (Derivation body (Delta.map (fun q => q.relabel Sum.inl)) (matrix raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) :=
  InternalClosedProgramsBindingProof.introduction body alpha 3 Delta _ h

theorem atRawApply (input suffix out needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (AtRaw input)))
    (hf : Nonempty (Derivation body Delta (fields input suffix out needle))) :
    Nonempty (Derivation body Delta (result input suffix out needle)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta
    (matrix input) (fun i => emb (![suffix,out,needle] i)) h
  rw [NumberedWindowInternalThinUncoveredCountBoundSyntaxProof.matrixWitness] at h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

theorem belowRawAt  (raw child : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw))) :
    Nonempty (Derivation body Delta (AtRaw child)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb child) h
  change Derivation body Delta (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (raw.relabel Sum.inl)).imp
      (rawPredicate)) (emb child)) at d
  rw [belowElimSyntax,rawPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowRawApply (input child suffix out needle : OTerm alpha)
    (h : Nonempty (Derivation body Delta (BelowRaw input)))
    (hl : Nonempty (Derivation body Delta (InternalLessThan.strictLess child input)))
    (hf : Nonempty (Derivation body Delta (fields child suffix out needle))) :
    Nonempty (Derivation body Delta (result child suffix out needle)) :=
  atRawApply child suffix out needle (belowRawAt input child h hl) hf

/-- The smaller-input hypothesis and its universal parameters are discharged
inside the original strong-induction derivation. -/
theorem rawInduction  (raw : OTerm alpha)
    (step : ∀ (beta : Type) (Theta : List (Formula beta)) (r : OTerm beta),
      Nonempty (Derivation body Theta (BelowRaw r)) →
      Nonempty (Derivation body Theta (AtRaw r))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  let theta : Formula (alpha ⊕ Fin 1) := rawPredicate
  have hs : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Delta.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (rawPredicate)) (.var (.inr 0)) :: Delta.map weaken)
      (AtRaw (.var (.inr 0))))
    rw [rawPredicateLift]
    exact step (alpha ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have derived : Nonempty (Derivation body Delta (SourceComputabilityFormulaSupportProof.allOne theta)) :=
    strongInduction theta hs
  obtain ⟨d⟩ := derived
  have e := Derivation.universalElimination (emb raw) d
  change Derivation body Delta (instantiate (rawPredicate) (emb raw)) at e
  rw [rawPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundBindingProof
