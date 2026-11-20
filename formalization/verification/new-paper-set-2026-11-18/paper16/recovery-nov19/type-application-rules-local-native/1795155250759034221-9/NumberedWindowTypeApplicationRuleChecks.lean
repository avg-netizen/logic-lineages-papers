module
public import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindTerm bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTerms)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst termSubstVar)
open ID1Completion.InternalTermSubstitutionSyntaxProof (termSubstRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets NumberedWindowTypeApplicationRuleTargets
open NumberedWindowTypeFormulaSubstitutionProof SourceComputabilityFormulaSupportProof

theorem exact_FormulaSubstitution : FormulaSubstitution := substitution

private theorem first {α : Type} (p : Program 3) (σ τ : Ty) (q u : OTerm α) :
    instantiate (allOne (condition p σ τ (q.relabel (fun a => Sum.inl (Sum.inl a)))
          (.var (.inl (.inr 0))) (.var (.inr 0)))) (emb u) =
      allOne (condition p σ τ (q.relabel Sum.inl) (u.relabel Sum.inl) (.var (.inr 0))) := by
  rw [instantiate,bindEmbedding,allEmbeddedSubst,conditionSubst]
  have both : (q.relabel (fun a => Sum.inl (Sum.inl a) : α → (α ⊕ Fin 1) ⊕ Fin 1)).subst
      (liftTerms (bindTerm u)) = q.relabel Sum.inl := by
    rw [termRelabelSubst]
    calc _ = (q.subst Term.var).relabel Sum.inl := (termSubstRelabel q Term.var Sum.inl).symm
         _ = q.relabel Sum.inl := by rw [termSubstVar]
  rw [both]
  rfl

theorem exact_ApplicationElimination : ApplicationElimination := by
  rintro body p σ τ α Γ q u v ⟨hf⟩ ⟨hg⟩ ⟨hu⟩
  have h1 := Derivation.universalElimination (emb u) hf
  rw [first] at h1
  have h2 := Derivation.universalElimination (emb v) h1
  rw [instantiate,bindEmbedding,conditionSubst,liftBind,liftBind,varBind] at h2
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h2 hg) hu⟩

theorem exact_ApplicationIntroduction : ApplicationIntroduction := by
  intro body p σ τ α Γ q h
  obtain ⟨d⟩ := h
  exact ⟨Derivation.universalIntroduction (Derivation.universalIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction d)))⟩

#print axioms exact_FormulaSubstitution
#print axioms exact_ApplicationElimination
#print axioms exact_ApplicationIntroduction
end LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
