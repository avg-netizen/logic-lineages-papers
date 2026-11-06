module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaInvariantProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus JointGammaInvariant SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalInvariantSelectionSupportProof InternalPositiveUnfoldingSupportProof

theorem actualInternalInvariantSelection : InternalInvariantSelectionTargets.ActualInternalInvariantSelection := by
  intro body α scalar multiset t
  obtain ⟨evenOut⟩ := ownBranchElimination body false scalar t
  obtain ⟨evenIn⟩ := ownBranchIntroduction body false scalar t
  obtain ⟨oddOut⟩ := ownBranchElimination body true multiset t
  obtain ⟨oddIn⟩ := ownBranchIntroduction body true multiset t
  obtain ⟨oddVac⟩ := oppositeBranch body false multiset t
  obtain ⟨evenVac⟩ := oppositeBranch body true scalar t
  constructor
  · apply Nonempty.intro
    apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      exact Derivation.implicationElimination (weakenClosed evenOut _)
        (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))
    · apply Derivation.implicationIntroduction
      exact Derivation.conjunctionIntroduction
        (Derivation.implicationElimination (weakenClosed evenIn _)
          (Derivation.hypothesis List.mem_cons_self)) (weakenClosed oddVac _)
  · apply Nonempty.intro
    apply Derivation.conjunctionIntroduction
    · apply Derivation.implicationIntroduction
      exact Derivation.implicationElimination (weakenClosed oddOut _)
        (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))
    · apply Derivation.implicationIntroduction
      exact Derivation.conjunctionIntroduction (weakenClosed evenVac _)
        (Derivation.implicationElimination (weakenClosed oddIn _)
          (Derivation.hypothesis List.mem_cons_self))

theorem actualInternalFiniteWindowSelection : InternalInvariantSelectionTargets.ActualInternalFiniteWindowSelection := by
  intro source context data S multiset t
  exact (actualInternalInvariantSelection (SourcePresentation.sourceBody source context)
    (Fin 2) (window data S) multiset t).1

/-- Composition of actual implications; no additional inference rule. -/
def implicationCompose {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    {p q r : Formula α} (d : Derivation body Gamma (p.imp q)) (e : Derivation body [] (q.imp r)) :
    Derivation body Gamma (p.imp r) := by
  apply Derivation.implicationIntroduction
  have hd : Derivation body (p :: Gamma) (p.imp q) :=
    Derivation.weakening (fun _ h => List.mem_cons_of_mem _ h) d
  exact Derivation.implicationElimination (weakenClosed e _)
    (Derivation.implicationElimination hd (Derivation.hypothesis List.mem_cons_self))

theorem actualSelectedInvariantInduction : InternalInvariantSelectionTargets.ActualSelectedInvariantInduction := by
  intro data context α Gamma scalar multiset t hstep
  obtain ⟨heven⟩ := (JointGammaInvariantProof.actualInternalTaggedInduction data context α Gamma
    scalar multiset (emb (tagTerm false t)) hstep).2
  obtain ⟨hodd⟩ := (JointGammaInvariantProof.actualInternalTaggedInduction data context α Gamma
    scalar multiset (emb (tagTerm true t)) hstep).2
  obtain ⟨⟨selectEven⟩,⟨selectOdd⟩⟩ := actualInternalInvariantSelection
    (SourcePresentation.sourceBody data context) α scalar multiset t
  change Derivation _ Gamma ((instantiate PositiveArithmeticSchemas.predicateAtObject
    (emb (tagTerm false t))).imp (instantiate (tagged scalar multiset) (emb (tagTerm false t)))) at heven
  change Derivation _ Gamma ((instantiate PositiveArithmeticSchemas.predicateAtObject
    (emb (tagTerm true t))).imp (instantiate (tagged scalar multiset) (emb (tagTerm true t)))) at hodd
  rw [instantiatePredicate] at heven hodd
  exact ⟨⟨implicationCompose heven (Derivation.conjunctionLeft selectEven)⟩,
    ⟨implicationCompose hodd (Derivation.conjunctionLeft selectOdd)⟩⟩

theorem actualFiniteWindowInduction : InternalInvariantSelectionTargets.ActualFiniteWindowInduction := by
  intro source context data S Gamma multiset t hstep
  exact (actualSelectedInvariantInduction source context (Fin 2) Gamma
    (window data S) multiset t hstep).1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionProof
