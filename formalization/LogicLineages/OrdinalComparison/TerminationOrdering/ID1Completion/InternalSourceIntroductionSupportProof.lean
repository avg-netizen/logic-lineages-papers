module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms
open InternalCalculus SourceEndpoint TaggedArithmeticOperators SourceComputabilityFormulaSupportProof
open InternalSourceInversionSupportProof InternalSourceIntroductionSyntaxProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalTagArithmeticProof

/-- Equality transport is exactly the ORIGINAL equality-elimination rule. -/
def transportPayload {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (p : Positive (Fin 2)) (c s t : OTerm α)
    (he : Derivation body Gamma (eqn s t)) (hp : Derivation body Gamma (payload p c s)) :
    Derivation body Gamma (payload p c t) := by
  have h := Derivation.equalityElimination
    (payload p (c.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb s) (emb t) he
  rw [payloadInstantiate,payloadInstantiate] at h
  exact h hp

theorem actualTaggedBranchIntroduction : InternalSourceIntroductionTargets.ActualTaggedBranchIntroduction := by
  intro body α odd p c t
  let x : OTerm (α ⊕ Fin 1) := t.relabel Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨inj⟩ := actualTagInjectivity body (α ⊕ Fin 1) odd x y
  rw [branchUnfold,tagRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let Gamma : List (Formula (α ⊕ Fin 1)) :=
    eqn (tagTerm odd x) (tagTerm odd y) :: [payload (tagPredicate odd p) c t].map weaken
  have he : Derivation body Gamma (eqn (tagTerm odd x) (tagTerm odd y)) :=
    Derivation.hypothesis List.mem_cons_self
  change Derivation body [] ((arithmeticEmbedding.onFormula ((tagTerm odd x).equal (tagTerm odd y))).imp
    (arithmeticEmbedding.onFormula (x.equal y))) at inj
  simp only [onEquality] at inj
  have hxy : Derivation body Gamma (eqn x y) :=
    Derivation.implicationElimination (weakenClosed inj Gamma) he
  have hp : Derivation body Gamma (weaken (payload (tagPredicate odd p) c t)) :=
    Derivation.hypothesis (by simp [Gamma])
  rw [weaken,payloadRelabel] at hp
  exact transportPayload (tagPredicate odd p) (c.relabel Sum.inl) x y hxy hp

theorem actualOppositeBranch : InternalSourceIntroductionTargets.ActualOppositeBranch := by
  intro body α odd p c t
  let x : OTerm (α ⊕ Fin 1) := t.relabel Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨disjointXY⟩ := actualTagsDisjoint body (α ⊕ Fin 1) x y
  obtain ⟨disjointYX⟩ := actualTagsDisjoint body (α ⊕ Fin 1) y x
  rw [branchUnfold,tagRelabel]
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  apply Derivation.explosion
  cases odd with
  | false =>
    have disjoint := disjointXY
    change Derivation body [] (arithmeticEmbedding.onFormula ((tagTerm false x).equal (tagTerm true y))).not at disjoint
    rw [onEquality] at disjoint
    exact Derivation.implicationElimination (weakenClosed disjoint _)
      (Derivation.hypothesis List.mem_cons_self)
  | true =>
    have disjoint := disjointYX
    change Derivation body [] (arithmeticEmbedding.onFormula ((tagTerm false y).equal (tagTerm true x))).not at disjoint
    rw [onEquality] at disjoint
    exact Derivation.implicationElimination (weakenClosed disjoint _)
      (InternalTagArithmeticSupportProof.symm (Derivation.hypothesis List.mem_cons_self))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSupportProof
