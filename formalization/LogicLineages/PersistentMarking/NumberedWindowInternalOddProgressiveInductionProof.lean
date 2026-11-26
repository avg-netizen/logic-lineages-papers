module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOddProgressiveInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution SourceComputabilityFormulaSupportProof
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus
open ID1Completion.InternalSliceInduction ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindTerm bindEmbedding liftBind varBind)

/-- The actual odd-edge induction hypothesis. The current multiset stays among
the parameters of the edge; the final bound variable is the smaller multiset
and occupies the distinguished invariant argument. -/
def oddLower {α : Type} (data : Data) (c : Nat) (x : OTerm (α ⊕ Fin 1))
    (theta : Formula (α ⊕ Fin 1)) : Formula (α ⊕ Fin 1) :=
  allOne ((edge data true c (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (liftPredicateFormula theta))

/-- Instantiate the true induction hypothesis with an arbitrary open smaller
multiset term. The original parameters, not the current multiset slot, are
retained by the invariant. -/
theorem exact_OriginalOddLowerInstance {α : Type} (data : Data) (c : Nat)
    (Γ : List (Formula (α ⊕ Fin 1))) (x y : OTerm (α ⊕ Fin 1))
    (theta : Formula (α ⊕ Fin 1)) :
    Nonempty (Derivation (sourceBody data c) Γ (oddLower data c x theta)) →
    Nonempty (Derivation (sourceBody data c) Γ (edge data true c x y)) →
    Nonempty (Derivation (sourceBody data c) Γ
      (theta.subst (Sum.elim (fun a => .var (.inl a)) (fun _ => emb y)))) := by
  rintro ⟨h⟩ ⟨hEdge⟩
  have edgeAt : instantiate
      (edge data true c (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb y) =
      edge data true c x y := by
    rw [instantiate, bindEmbedding, ID1Completion.InternalAccessibilityRulesSyntaxProof.edgeSubst,
      liftBind, varBind]
  have thetaAt : instantiate (liftPredicateFormula theta) (emb y) =
      theta.subst (Sum.elim (fun a => .var (.inl a)) (fun _ => emb y)) := by
    rw [instantiate, liftPredicateFormula,
      ID1Completion.InternalBinderTransportProof.actualRelabelSubstitution] <;>
      first | rfl | (congr 1; funext i; cases i <;> rfl)
  have hi : Derivation (sourceBody data c) Γ
      (instantiate ((edge data true c (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
        (liftPredicateFormula theta)) (emb y)) :=
    Derivation.universalElimination (emb y) h
  change Derivation (sourceBody data c) Γ
    ((instantiate (edge data true c (x.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb y)).imp
      (instantiate (liftPredicateFormula theta) (emb y))) at hi
  rw [edgeAt, thetaAt] at hi
  exact ⟨Derivation.implicationElimination hi hEdge⟩

/-- Original ID1 induction on one actual odd multiset code. Its open progress
premise has two hypotheses: the actual typed carrier and the invariant at all
actual strict successors. This is not an origin-split or union principle. -/
def ActualOriginalOddProgressiveInduction : Prop :=
  ∀ (data : Data) (c : Nat) (α : Type) (Γ : List (Formula α))
    (theta : Formula (α ⊕ Fin 1)) (t : OTerm α),
    let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    Nonempty (Derivation (sourceBody data c)
      (carrier data true c x :: oddLower data c x theta :: Γ.map weaken) theta) →
    Nonempty (Derivation (sourceBody data c) Γ
      ((membership true t).imp (instantiate theta (emb t))))

theorem exact_ActualOriginalOddProgressiveInduction : ActualOriginalOddProgressiveInduction := by
  intro data c α Γ theta t
  dsimp only
  rintro ⟨progress⟩
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let typed := carrier data true c x
  let lower := oddLower data c x theta
  let combined := replacedBody (sliceBody data c true) theta
  let delta := combined :: Γ.map weaken
  have combinedEq : combined = typed ⊓ lower :=
    ID1Completion.InternalSliceInductionSyntaxProof.sliceReplacement data c true theta
  have closure : Nonempty (Derivation (sourceBody data c) delta theta) := by
    have h : Derivation (sourceBody data c) delta combined :=
      Derivation.hypothesis List.mem_cons_self
    have pair : Derivation (sourceBody data c) delta (typed ⊓ lower) :=
      Eq.mp (congrArg (Derivation (sourceBody data c) delta) combinedEq) h
    have work : Derivation (sourceBody data c) (Γ.map weaken) (lower.imp (typed.imp theta)) :=
      Derivation.implicationIntroduction (Derivation.implicationIntroduction progress)
    have localWork : Derivation (sourceBody data c) delta (lower.imp (typed.imp theta)) :=
      Derivation.weakening (fun _ hp => List.mem_cons_of_mem _ hp) work
    exact ⟨Derivation.implicationElimination
      (Derivation.implicationElimination localWork (Derivation.conjunctionRight pair))
      (Derivation.conjunctionLeft pair)⟩
  exact ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction
    data c α Γ true theta t closure

#print axioms exact_OriginalOddLowerInstance
#print axioms exact_ActualOriginalOddProgressiveInduction

end LogicLineages.PersistentMarking.NumberedWindowInternalOddProgressiveInductionProof
