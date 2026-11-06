module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms PositiveArithmeticPredicateSubstitution
open InternalCalculus JointGammaInvariant SourceComputabilityFormulaSupportProof
open InternalBinderTransportProof InternalSourceInversionSupportProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof InternalTagArithmeticProof InternalSourceIntroductionSyntaxProof
open InternalInvariantSelectionSyntaxProof InternalPositiveUnfoldingSupportProof

theorem ownBranchElimination (body : Positive (Fin 1)) {α : Type} (odd : Bool)
    (phi : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    Nonempty (Derivation body []
      ((instantiate (branch odd phi) (emb (tagTerm odd t))).imp (instantiate phi (emb t)))) := by
  rw [branchInstantiate,tagRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  have h : Derivation body
      [allOne ((eqn (tagTerm odd (t.relabel Sum.inl)) (tagTerm odd (.var (.inr (0 : Fin 1))))).imp phi)]
      (allOne ((eqn (tagTerm odd (t.relabel Sum.inl)) (tagTerm odd (.var (.inr (0 : Fin 1))))).imp phi)) :=
    Derivation.hypothesis List.mem_cons_self
  have k := Derivation.universalElimination (emb t) h
  change Derivation body _ ((instantiate (eqn (tagTerm odd (t.relabel Sum.inl))
    (tagTerm odd (.var (.inr (0 : Fin 1))))) (emb t)).imp (instantiate phi (emb t))) at k
  rw [eqnInstantiate,tagSubstitution,tagSubstitution,liftBind,varBind] at k
  exact Derivation.implicationElimination k (refl (tagTerm odd t))

theorem ownBranchIntroduction (body : Positive (Fin 1)) {α : Type} (odd : Bool)
    (phi : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    Nonempty (Derivation body []
      ((instantiate phi (emb t)).imp (instantiate (branch odd phi) (emb (tagTerm odd t))))) := by
  let x : OTerm (α ⊕ Fin 1) := t.relabel Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨inj⟩ := actualTagInjectivity body (α ⊕ Fin 1) odd x y
  change Derivation body [] ((arithmeticEmbedding.onFormula ((tagTerm odd x).equal (tagTerm odd y))).imp
    (arithmeticEmbedding.onFormula (x.equal y))) at inj
  simp only [onEquality] at inj
  rw [branchInstantiate,tagRelabel]
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let Gamma : List (Formula (α ⊕ Fin 1)) :=
    eqn (tagTerm odd x) (tagTerm odd y) :: [instantiate phi (emb t)].map weaken
  have he : Derivation body Gamma (eqn (tagTerm odd x) (tagTerm odd y)) :=
    Derivation.hypothesis List.mem_cons_self
  have hxy : Derivation body Gamma (eqn x y) :=
    Derivation.implicationElimination (weakenClosed inj Gamma) he
  have hp : Derivation body Gamma (weaken (instantiate phi (emb t))) :=
    Derivation.hypothesis (by simp [Gamma])
  rw [weaken,← instantiateLift] at hp
  have h := Derivation.equalityElimination (liftPredicateFormula phi) (emb x) (emb y) hxy hp
  change Derivation body Gamma (instantiate (liftPredicateFormula phi) (.var (.inr (0 : Fin 1)))) at h
  rw [actualFreshInstantiation] at h
  exact h

theorem oppositeBranch (body : Positive (Fin 1)) {α : Type} (odd : Bool)
    (phi : Formula (α ⊕ Fin 1)) (t : OTerm α) :
    Nonempty (Derivation body [] (instantiate (branch (!odd) phi) (emb (tagTerm odd t)))) := by
  let x : OTerm (α ⊕ Fin 1) := t.relabel Sum.inl
  let y : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  obtain ⟨disjointXY⟩ := actualTagsDisjoint body (α ⊕ Fin 1) x y
  obtain ⟨disjointYX⟩ := actualTagsDisjoint body (α ⊕ Fin 1) y x
  rw [branchInstantiate,tagRelabel]
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  apply Derivation.explosion
  cases odd with
  | false =>
    change Derivation body [] (arithmeticEmbedding.onFormula ((tagTerm false x).equal (tagTerm true y))).not at disjointXY
    rw [onEquality] at disjointXY
    exact Derivation.implicationElimination (weakenClosed disjointXY _)
      (Derivation.hypothesis List.mem_cons_self)
  | true =>
    change Derivation body [] (arithmeticEmbedding.onFormula ((tagTerm false y).equal (tagTerm true x))).not at disjointYX
    rw [onEquality] at disjointYX
    exact Derivation.implicationElimination (weakenClosed disjointYX _)
      (InternalTagArithmeticSupportProof.symm (Derivation.hypothesis List.mem_cons_self))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalInvariantSelectionSupportProof
