module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open InternalCalculus SourceEndpoint TaggedArithmeticOperators InternalTermSubstitutionSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof

theorem actualFormulaSubstitutionComposition : InternalTermSubstitutionTargets.ActualFormulaSubstitutionComposition := by
  intro α β γ phi ts us
  exact formulaSubstComposition phi ts us

theorem actualUniversalSubstitution : InternalTermSubstitutionTargets.ActualUniversalSubstitution := by
  intro α β phi ts
  change ((BoundedFormula.relabel id phi).subst ts).all = _
  rw [substBind]
  rfl

theorem predicateSubstitution {α β : Type} (t : OrdinaryArithmetic.Term α)
    (ts : α → OrdinaryArithmetic.Term β) :
    (Positive.predicate (t.subst ts)).formula =
      (Positive.predicate t).formula.subst (fun a => arithmeticEmbedding.onTerm (ts a)) := by
  simp only [Positive.formula,Relations.formula₁,Relations.formula,Relations.boundedFormula,
    BoundedFormula.subst,BoundedFormula.mapTermRel]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Matrix.cons_val_zero,onTermSubst]
  rw [termSubstRelabel,termRelabelSubst]
  rfl

theorem positiveSubstitution {α : Type} (p : Positive α) :
    ∀ (β : Type) (ts : α → OrdinaryArithmetic.Term β),
    (substitutePositive ts p).formula = p.formula.subst (fun a => arithmeticEmbedding.onTerm (ts a)) := by
  induction p with
  | arithmetic phi => intro β ts; exact onFormulaSubst arithmeticEmbedding phi ts
  | predicate t => intro β ts; exact predicateSubstitution t ts
  | conj p q ihp ihq =>
    intro β ts
    change (substitutePositive ts p).formula ⊓ (substitutePositive ts q).formula = _
    rw [ihp,ihq]
    rfl
  | guarded guard p ih =>
    intro β ts
    change (arithmeticEmbedding.onFormula (guard.subst ts)).imp (substitutePositive ts p).formula = _
    rw [ih]
    have hg : arithmeticEmbedding.onFormula (guard.subst ts) =
        (arithmeticEmbedding.onFormula guard).subst (fun a => arithmeticEmbedding.onTerm (ts a)) :=
      onFormulaSubst arithmeticEmbedding guard ts
    rw [hg]
    rfl
  | all p ih =>
    intro β ts
    change allOne (substitutePositive _ p).formula = (allOne p.formula).subst _
    rw [ih,actualUniversalSubstitution]
    congr 1
    congr 1
    funext i
    cases i with
    | inl a => exact onTermRelabel arithmeticEmbedding Sum.inl (ts a)
    | inr i => rfl

theorem actualPositiveSubstitution : InternalTermSubstitutionTargets.ActualPositiveSubstitution := by
  intro α β p ts
  exact positiveSubstitution p β ts

theorem numeralSubstitution {α β : Type} (n : Nat) (ts : α → Term β) :
    (arithmeticEmbedding.onTerm (numeral n : OrdinaryArithmetic.Term α)).subst ts =
      arithmeticEmbedding.onTerm (numeral n : OrdinaryArithmetic.Term β) := by
  induction n with
  | zero =>
    simp only [numeral,OrdinaryArithmetic.zeroTerm,LHom.onTerm,Term.subst]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    simp only [numeral,OrdinaryArithmetic.succTerm,Functions.apply₁,LHom.onTerm,Term.subst]
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact ih

theorem actualSourceBodyInstantiation : InternalTermSubstitutionTargets.ActualSourceBodyInstantiation := by
  intro data context α t
  rw [bodyInvariantFormula,instantiate,actualRelabelSubstitution]
  change (SourcePresentation.sourceBody data context).formula.subst (fun _ => arithmeticEmbedding.onTerm t) = _
  rw [SourcePresentation.sourceBody,actualPositiveSubstitution,formulaSubstComposition,
    actualPositiveSubstitution]
  congr 1
  funext i
  exact Fin.cases (numeralSubstitution context _)
    (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem actualExplicitSourceUnfolding : InternalTermSubstitutionTargets.ActualExplicitSourceUnfolding := by
  intro data context α t
  have h := InternalPositiveUnfoldingProof.actualOriginalSourceUnfolding data context α
    (arithmeticEmbedding.onTerm t)
  rw [instantiatePredicate,actualSourceBodyInstantiation] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
