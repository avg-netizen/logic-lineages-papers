module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTChoiceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalBoundedCRTSyntaxProof
open InternalRelationalCRT InternalRelationalCRTChoiceProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof InternalDerivationRenamingSyntaxProof
open InternalLeastNumberSyntaxProof InternalModularArithmeticProof InternalBinaryCRTSyntaxProof
open InternalGraphCompositionSyntaxProof InternalQuotientComparisonSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalSourceIntroductionSyntaxProof

theorem relationLiftRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (j : α → β) :
    (R.relabel (Sum.map (Sum.map (Sum.inl : α → α ⊕ Fin 1) id) id)).relabel
      (Sum.map (Sum.map (Sum.map j id) id) id) =
    (R.relabel (Sum.map (Sum.map j id) id)).relabel (Sum.map (Sum.map Sum.inl id) id) := by
  rw [formulaRelabelComposition,formulaRelabelComposition]
  congr 1
  funext x
  rcases x with (x | i) | j <;> rfl

theorem relationLiftSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (ts : α → OTerm β) :
    (R.relabel (Sum.map (Sum.map Sum.inl id) id)).subst
      (fun x => emb (liftTerms (liftTerms (liftTerms ts)) x)) =
    Formula.relabel (Sum.map (Sum.map (Sum.inl : β → β ⊕ Fin 1) id) id)
      (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) := by
  rw [actualRelabelSubstitution,formulaSubstRelabel]
  congr 1
  funext x
  rcases x with (a | i) | j
  · simp only [Function.comp_apply,liftTerms,Sum.map_inl,Sum.elim_inl]
    rw [← onTermRelabel]
    congr 1
    simp only [Term.relabel_relabel]
    rfl
  · rfl
  · rfl

theorem relationLiftBind {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (s : OTerm α) :
    (R.relabel (Sum.map (Sum.map Sum.inl id) id)).subst
      (fun x => emb (liftTerms (liftTerms (bindTerm s)) x)) = R := by
  rw [actualRelabelSubstitution]
  have he : (fun x => emb (liftTerms (liftTerms (bindTerm s)) x)) ∘
      Sum.map (Sum.map Sum.inl id) id = Term.var := by
    funext x; rcases x with (a | i) | j <;> rfl
  rw [he,formulaSubstVar]

theorem relationLiftNext {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) :
    (R.relabel (Sum.map (Sum.map Sum.inl id) id)).subst
      (fun x => emb (liftTerms (liftTerms (nextTerm (α := α))) x)) =
    R.relabel (Sum.map (Sum.map Sum.inl id) id) := by
  rw [actualRelabelSubstitution,formulaRelabelAsSubst]
  congr 1
  funext x; rcases x with (a | i) | j <;> rfl

theorem availableBelowRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (availableBelow R n).relabel j = availableBelow (R.relabel (Sum.map (Sum.map j id) id)) (n.relabel j) := by
  unfold availableBelow
  rw [boundedRename,existsRename]

theorem availableBelowSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (ts : α → OTerm β) :
    (availableBelow R n).subst (fun x => emb (ts x)) =
      availableBelow (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (n.subst ts) := by
  unfold availableBelow
  rw [boundedSubst,existsSubst,liftEmbedding]

theorem residuesBelowRename {α β : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (c n : OTerm α) (j : α → β) :
    (residuesBelow t R c n).relabel j = residuesBelow (t.relabel (Sum.map j id))
      (R.relabel (Sum.map (Sum.map j id) id)) (c.relabel j) (n.relabel j) := by
  unfold residuesBelow
  rw [boundedRename,chosenRename]
  simp only [sucRelabel,Term.relabel_relabel,mapInl]

theorem residuesBelowSubst {α β : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (c n : OTerm α) (ts : α → OTerm β) :
    (residuesBelow t R c n).subst (fun x => emb (ts x)) =
      residuesBelow (t.subst (liftTerms ts))
        (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (c.subst ts) (n.subst ts) := by
  unfold residuesBelow
  rw [boundedSubst,chosenSubst,sucSubst,liftSubst]

theorem solutionRename {α β : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (solution t R n).relabel j = solution (t.relabel (Sum.map j id))
      (R.relabel (Sum.map (Sum.map j id) id)) (n.relabel j) := by
  unfold solution
  rw [existsRename,residuesBelowRename,familyLiftRename,relationLiftRename]
  simp only [Term.relabel_relabel,mapInl,varMap]

theorem solutionSubst {α β : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) (ts : α → OTerm β) :
    (solution t R n).subst (fun x => emb (ts x)) = solution (t.subst (liftTerms ts))
      (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (n.subst ts) := by
  unfold solution
  rw [existsSubst,liftEmbedding,residuesBelowSubst,relationLiftSubst]
  simp only [liftedFamilySubst,liftSubst]
  rfl

theorem availableBelowInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) :
    instantiate (availableBelow (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0))) (emb n) =
      availableBelow R n := by
  rw [instantiate,bindEmbedding,availableBelowSubst,relationLiftBind,varBind]

theorem solutionInstantiate {α : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) :
    instantiate (solution (t.relabel (Sum.map Sum.inl id))
      (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0))) (emb n) = solution t R n := by
  rw [instantiate,bindEmbedding,solutionSubst,relationLiftBind,termLiftBind,varBind]

theorem solutionMatrixInstantiate {α : Type} (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n c : OTerm α) :
    instantiate (residuesBelow (t.relabel (Sum.map Sum.inl id))
      (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0)) (n.relabel Sum.inl)) (emb c) =
      residuesBelow t R c n := by
  rw [instantiate,bindEmbedding,residuesBelowSubst,relationLiftBind,termLiftBind,varBind,liftBind]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem solutionIntroduction (t : OTerm (α ⊕ Fin 1)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n c : OTerm α)
    (h : Nonempty (Derivation body Gamma (residuesBelow t R c n))) :
    Nonempty (Derivation body Gamma (solution t R n)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb c)
  rw [solutionMatrixInstantiate]
  exact h

theorem solutionCases (Gamma : List (Formula α)) (t : OTerm (α ⊕ Fin 1))
    (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (solution t R n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (c : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (residuesBelow (t.relabel (Sum.map j id))
        (R.relabel (Sum.map (Sum.map j id) id)) c (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h hk⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTSyntaxProof
