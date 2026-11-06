module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution PositiveArithmeticSchemas
open InternalCalculus InternalBinderTransportSyntaxProof InternalBinderTransportProof

 theorem renameComposition {L : Language} {α β γ : Type} (f : α → β) (g : β → γ)
    {k : Nat} (phi : L.BoundedFormula α k) : rename g (rename f phi) = rename (g ∘ f) phi := by
  have ht (j : Nat) (t : L.Term (α ⊕ Fin j)) :
      (t.relabel (Sum.map f id)).relabel (Sum.map g id) = t.relabel (Sum.map (g ∘ f) id) := by
    rw [Term.relabel_relabel]
    congr 1
    funext i
    cases i <;> rfl
  induction phi with
  | falsum => rfl
  | equal t u => simp only [rename,BoundedFormula.mapTermRel,ht]
  | rel r ts => simp only [rename,BoundedFormula.mapTermRel,ht]; rfl
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih => exact congrArg BoundedFormula.all ih

theorem formulaRelabelComposition {L : Language} {α β γ : Type} (f : α → β) (g : β → γ)
    (phi : L.Formula α) : (phi.relabel f).relabel g = phi.relabel (g ∘ f) := by
  rw [formulaRelabel,formulaRelabel,formulaRelabel,renameComposition]

theorem bodyInvariantFormula (body : Positive (Fin 1)) (α : Type) :
    (bodyWithParameters body α).formula = body.formula.relabel (Sum.inr : Fin 1 → α ⊕ Fin 1) := by
  exact actualPositiveRenaming (Fin 1) (α ⊕ Fin 1) Sum.inr body

theorem liftBodyInvariant (body : Positive (Fin 1)) (α : Type) :
    liftPredicateFormula (bodyWithParameters body α).formula =
      (bodyWithParameters body (α ⊕ Fin 1)).formula := by
  rw [liftPredicateFormula,bodyInvariantFormula,bodyInvariantFormula,formulaRelabelComposition]
  rfl

theorem instantiatePredicate {α : Type} (t : OrdinaryArithmetic.Term α) :
    instantiate (predicateAtObject (α := α)) (arithmeticEmbedding.onTerm t) =
      (Positive.predicate t).formula := by
  simp only [instantiate,predicateAtObject,Positive.formula,Relations.formula₁,Relations.formula,
    Relations.boundedFormula,BoundedFormula.subst,BoundedFormula.mapTermRel,LHom.onTerm]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- Context extension of a closed proof; no extra logical rule. -/
def weakenClosed {body : Positive (Fin 1)} {α : Type} {phi : Formula α}
    (d : Derivation body [] phi) (Gamma : List (Formula α)) : Derivation body Gamma phi :=
  Derivation.weakening (fun _ h => False.elim (List.not_mem_nil h)) d

theorem positiveContraction (body : Positive (Fin 1)) {α : Type} (p : Positive α) :
    Nonempty (Derivation body []
      ((substitutePredicate p (bodyWithParameters body α).formula).imp p.formula)) := by
  induction p with
  | arithmetic phi =>
    exact ⟨Derivation.implicationIntroduction (Derivation.hypothesis (List.mem_cons_self))⟩
  | @predicate α t =>
    have d := Derivation.universalElimination (arithmeticEmbedding.onTerm t)
      (Derivation.inductiveClosure (body := body) (α := α) (Gamma := []))
    change Derivation body []
      ((instantiate (bodyWithParameters body α).formula (arithmeticEmbedding.onTerm t)).imp
        (instantiate predicateAtObject (arithmeticEmbedding.onTerm t))) at d
    rw [instantiatePredicate] at d
    exact ⟨d⟩
  | conj p q ihp ihq =>
    obtain ⟨dp⟩ := ihp
    obtain ⟨dq⟩ := ihq
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    have h : Derivation body
        [substitutePredicate (.conj p q) (bodyWithParameters body _).formula]
        (substitutePredicate (.conj p q) (bodyWithParameters body _).formula) :=
      Derivation.hypothesis List.mem_cons_self
    exact Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (weakenClosed dp _) (Derivation.conjunctionLeft h))
      (Derivation.implicationElimination (weakenClosed dq _) (Derivation.conjunctionRight h))
  | guarded guard p ih =>
    obtain ⟨d⟩ := ih
    apply Nonempty.intro
    apply Derivation.implicationIntroduction
    apply Derivation.implicationIntroduction
    let B := arithmeticEmbedding.onFormula guard
    let A := substitutePredicate p (bodyWithParameters body _).formula
    have hg : Derivation body [B, B.imp A] B := Derivation.hypothesis List.mem_cons_self
    have ha : Derivation body [B, B.imp A] (B.imp A) :=
      Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
    exact Derivation.implicationElimination (weakenClosed d _)
      (Derivation.implicationElimination ha hg)
  | @all α p ih =>
    change Nonempty (Derivation body []
      ((SourceComputabilityFormulaSupportProof.allOne
        (substitutePredicate p (liftPredicateFormula (bodyWithParameters body α).formula))).imp
          (SourceComputabilityFormulaSupportProof.allOne p.formula)))
    rw [liftBodyInvariant]
    exact actualInternalUniversalTransport body α _ _ ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
