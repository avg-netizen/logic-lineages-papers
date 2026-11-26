module
public import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb suc z sucSubst zSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst liftTerms allEmbeddedSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst)
open ID1Completion.InternalTermSubstitutionSyntaxProof (termSubstRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets NumberedWindowTypeApplicationRuleTargets
open SourceComputabilityFormulaSupportProof (allOne)

theorem acceptsSubst {α β : Type} (p : Program 3) (q u v : OTerm α) (ts : α → OTerm β) :
    (accepts p q u v).subst (fun i => emb (ts i)) = accepts p (q.subst ts) (u.subst ts) (v.subst ts) := by
  change (programGraph p (suc z) ![q,u,v]).subst _ =
    programGraph p (suc z) ![q.subst ts,u.subst ts,v.subst ts]
  rw [programSubst, sucSubst, zSubst]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i

theorem impSubst {α β : Type} (f g : Formula α) (ts : α → Term β) :
    (f.imp g).subst ts = (f.subst ts).imp (g.subst ts) := rfl

theorem substitution : FormulaSubstitution := by
  intro p τ
  induction τ with
  | ground =>
    intro α β q ts
    exact membershipSubst false q ts
  | arrow σ τ ihσ ihτ =>
    intro α β q ts
    simp only [formula, allEmbeddedSubst, impSubst, acceptsSubst, ihσ, ihτ]
    have both :
        (q.relabel (fun a => Sum.inl (Sum.inl a) : α → (α ⊕ Fin 1) ⊕ Fin 1)).subst
          (liftTerms (liftTerms ts)) =
        (q.subst ts).relabel (fun a => Sum.inl (Sum.inl a)) := by
      rw [termRelabelSubst,termSubstRelabel]
      congr 1
      funext a
      exact Term.relabel_relabel Sum.inl Sum.inl (ts a)
    rw [both]
    rfl

def condition {α : Type} (p : Program 3) (σ τ : Ty) (q u v : OTerm α) : Formula α :=
  (accepts p q u v).imp ((formula p σ u).imp (formula p τ v))

theorem conditionSubst {α β : Type} (p : Program 3) (σ τ : Ty) (q u v : OTerm α) (ts : α → OTerm β) :
    (condition p σ τ q u v).subst (fun i => emb (ts i)) =
      condition p σ τ (q.subst ts) (u.subst ts) (v.subst ts) := by
  simp only [condition, impSubst, acceptsSubst, substitution]

end LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
