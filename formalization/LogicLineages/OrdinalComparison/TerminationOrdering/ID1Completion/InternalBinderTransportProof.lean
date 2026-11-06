module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticPredicateSubstitution
open InternalCalculus SourceComputabilityFormulaSupportProof InternalBinderTransportSyntaxProof

theorem actualRelabelSubstitution : InternalBinderTransportTargets.ActualRelabelSubstitution := by
  intro α β γ phi f ts
  rw [formulaRelabel]
  exact renameSubst phi f ts

theorem actualUniversalRenaming : InternalBinderTransportTargets.ActualUniversalRenaming := by
  intro α β f phi
  rw [formulaRelabel]
  change (rename f (BoundedFormula.relabel id phi)).all = _
  rw [renameBind,← formulaRelabel]
  rfl

theorem actualFreshInstantiation : InternalBinderTransportTargets.ActualFreshInstantiation := by
  intro α phi
  rw [instantiate,liftPredicateFormula,actualRelabelSubstitution]
  have hf : (Sum.elim Term.var (fun _ : Fin 1 => (.var (.inr 0) : Term (α ⊕ Fin 1)))) ∘
      Sum.map (Sum.inl : α → α ⊕ Fin 1) id = Term.var := by
    funext i
    cases i with
    | inl a => rfl
    | inr a =>
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      rfl
  rw [hf,formulaSubstVar]

theorem arithmeticRename {α β : Type} (f : α → β) (phi : OrdinaryArithmetic.Formula α) :
    arithmeticEmbedding.onFormula (phi.relabel f) = (arithmeticEmbedding.onFormula phi).relabel f := by
  rw [formulaRelabel,formulaRelabel]
  exact onFormulaRename arithmeticEmbedding f phi

theorem predicateRename {α β : Type} (f : α → β) (t : OrdinaryArithmetic.Term α) :
    (Positive.predicate (t.relabel f)).formula = (Positive.predicate t).formula.relabel f := by
  rw [formulaRelabel]
  simp only [Positive.formula,Relations.formula₁,Relations.formula,Relations.boundedFormula,
    rename,BoundedFormula.mapTermRel]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Matrix.cons_val_zero,onTermRelabel,Term.relabel_relabel]
  rfl

theorem positiveRenaming {α : Type} (p : Positive α) :
    ∀ (β : Type) (f : α → β),
    (PositiveArithmeticTransforms.relabel f p).formula = p.formula.relabel f := by
  induction p with
  | arithmetic phi => intro β f; exact arithmeticRename f phi
  | predicate t => intro β f; exact predicateRename f t
  | conj p q ihp ihq =>
    intro β f
    change (PositiveArithmeticTransforms.relabel f p).formula ⊓
      (PositiveArithmeticTransforms.relabel f q).formula = (p.formula ⊓ q.formula).relabel f
    rw [ihp,ihq]
    rfl
  | guarded phi p ih =>
    intro β f
    change (arithmeticEmbedding.onFormula (phi.relabel f)).imp
      (PositiveArithmeticTransforms.relabel f p).formula =
      ((arithmeticEmbedding.onFormula phi).imp p.formula).relabel f
    rw [arithmeticRename,ih]
    rfl
  | all p ih =>
    intro β f
    change allOne (PositiveArithmeticTransforms.relabel (Sum.map f id) p).formula =
      (allOne p.formula).relabel f
    rw [ih,actualUniversalRenaming]

theorem actualPositiveRenaming : InternalBinderTransportTargets.ActualPositiveRenaming := by
  intro α β f p
  exact positiveRenaming p β f

theorem actualInternalUniversalTransport : InternalBinderTransportTargets.ActualInternalUniversalTransport := by
  intro body α phi psi ⟨d⟩
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  apply Derivation.universalIntroduction
  have hphi : Derivation body ([allOne phi].map weaken) phi := by
    have h : Derivation body ([allOne phi].map weaken) (weaken (allOne phi)) :=
      Derivation.hypothesis (by simp)
    rw [weaken,actualUniversalRenaming] at h
    have he := Derivation.universalElimination (.var (.inr 0)) h
    change Derivation body _ (instantiate (liftPredicateFormula phi) (.var (.inr 0))) at he
    rw [actualFreshInstantiation] at he
    exact he
  exact Derivation.implicationElimination
    (Derivation.weakening (fun p hp => False.elim (List.not_mem_nil hp)) d) hphi

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
