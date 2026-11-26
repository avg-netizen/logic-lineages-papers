module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
public import LogicLineages.PersistentMarking.NumberedWindowTypeFormulaSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeSubst edgeExists)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalMatchReductionTargets NumberedWindowInternalDownwardTargets
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowTypeFormulaSubstitutionProof (acceptsSubst)

private theorem acceptsRename {α β : Type} (p : Program 3) (x w y : OTerm α) (j : α → β) :
    (accepts p x w y).relabel j = accepts p (x.relabel j) (w.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (accepts p x w y).subst (fun a => emb (.var (j a))) = _
  rw [acceptsSubst, ← termRelabelAsSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

private theorem edgeRename {α β : Type} (s : ID1Completion.SourcePresentation.Data)
    (c : Nat) (x y : OTerm α) (j : α → β) :
    (edge s false c x y).relabel j = edge s false c (x.relabel j) (y.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (edge s false c x y).subst (fun a => emb (.var (j a))) = _
  rw [edgeSubst, ← termRelabelAsSubst, ← termRelabelAsSubst]

private theorem matchedRename {α β : Type} (s : ID1Completion.SourcePresentation.Data) (p : Program 3)
    (c : Nat) (f u v : OTerm α) (j : α → β) :
    (matched s p c f u v).relabel j = matched s p c (f.relabel j) (u.relabel j) (v.relabel j) := by
  simp only [matched,existsRename,conjunctionRename,acceptsRename,edgeRename,Term.relabel_relabel]
  rfl

private theorem unpackEdge (i j : Program 1) (r d : Program 3) (c : Nat)
    {body : PositiveArithmeticOperators.Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (x y : OTerm α)
    (h : Nonempty (Derivation body Γ (suppliedEdge r x y))) :
    Nonempty (Derivation body Γ (edge (data i j r d) false c x y)) := by
  obtain ⟨src⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialElimination src
  change Derivation _ _ ((edge _ false c x y).relabel Sum.inl)
  rw [edgeRename]
  have hc := (NumberedWindowInternalCoordinateChecks.exact_CertificateRules i j r d false c
    body _ _ (x.relabel Sum.inl) (y.relabel Sum.inl) (.var (.inr 0))).mpr
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact Classical.choice (ID1Completion.InternalAccessibilityRulesProof.edgeIntroduction hc)

private theorem unpackMatch (i j : Program 1) (r d p : Program 3) (c : Nat)
    {body : PositiveArithmeticOperators.Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (f u v : OTerm α) (h : Nonempty (Derivation body Γ (suppliedMatch p r f u v))) :
    Nonempty (Derivation body Γ (matched (data i j r d) p c f u v)) := by
  obtain ⟨src⟩ := h
  let b : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := accepts p (f.relabel Sum.inl) (u.relabel Sum.inl) b ⊓ suppliedEdge r b (v.relabel Sum.inl)
  let Δ := A :: Γ.map weaken
  have pair : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := unpackEdge i j r d c b (v.relabel Sum.inl) ⟨Derivation.conjunctionRight pair⟩
  apply Nonempty.intro
  apply Derivation.existentialElimination src
  change Derivation body Δ ((matched _ p c f u v).relabel Sum.inl)
  rw [matchedRename]
  apply Derivation.existentialIntroduction (emb b)
  rw [instantiate,bindEmbedding,conjunctionSubst,acceptsSubst,edgeSubst]
  simp only [liftBind,varBind]
  exact Derivation.conjunctionIntroduction (Derivation.conjunctionLeft pair) e

theorem exact_MatchingReduction : MatchingReduction := by
  intro i j r d p c raw α Γ f g u v hedge hApp
  obtain ⟨old⟩ := hedge
  rw [edgeExists] at old
  let body := ID1Completion.SourcePresentation.sourceBody (data i j r d) c
  let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := certificate (data i j r d) false c (f.relabel Sum.inl) (g.relabel Sum.inl) w
  let Δ := A :: Γ.map weaken
  have present := (NumberedWindowInternalCoordinateChecks.exact_CertificateRules i j r d false c
    body _ Δ _ _ w).mp ⟨Derivation.hypothesis List.mem_cons_self⟩
  have happ := ID1Completion.InternalGraphCompositionFunctionalityProof.renameInto hApp Sum.inl Δ
    (fun a ha => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
  rw [acceptsRename] at happ
  obtain ⟨input⟩ := present
  obtain ⟨application⟩ := happ
  have h := ID1Completion.InternalRecursionClosureLogicProof.closedApply
    (raw _ (f.relabel Sum.inl) (g.relabel Sum.inl) (u.relabel Sum.inl) (v.relabel Sum.inl) w)
    ⟨Derivation.conjunctionIntroduction input application⟩
  obtain ⟨out⟩ := unpackMatch i j r d p c _ _ _ h
  apply Nonempty.intro
  apply Derivation.existentialElimination old
  change Derivation body Δ ((matched _ p c f u v).relabel Sum.inl)
  rw [matchedRename]
  exact out

#print axioms exact_MatchingReduction
end LogicLineages.PersistentMarking.NumberedWindowInternalMatchReductionChecks
