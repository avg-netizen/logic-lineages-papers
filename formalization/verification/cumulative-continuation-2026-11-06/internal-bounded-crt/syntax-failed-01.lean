module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinaryCRTProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalBoundedCRT
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof InternalDerivationRenamingSyntaxProof
open InternalLeastNumberSyntaxProof InternalModularArithmeticProof InternalBinaryCRTSyntaxProof

theorem familyLiftRename {α β : Type} (t : OTerm (α ⊕ Fin 1)) (j : α → β) :
    (t.relabel (Sum.map Sum.inl id)).relabel (Sum.map (Sum.map j id) id) =
      (t.relabel (Sum.map j id)).relabel (Sum.map Sum.inl id) := by
  rw [Term.relabel_relabel,Term.relabel_relabel]
  congr 1
  funext x; cases x <;> rfl

theorem pairwiseBelowRename {α β : Type} (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (pairwiseBelow t n).relabel j = pairwiseBelow (t.relabel (Sum.map j id)) (n.relabel j) := by
  unfold pairwiseBelow
  simp only [boundedRename,coprimeBelowRename,sucRelabel,familyLiftRename,varMap]

theorem pairwiseBelowSubst {α β : Type} (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) (ts : α → OTerm β) :
    (pairwiseBelow t n).subst (fun x => emb (ts x)) =
      pairwiseBelow (t.subst (liftTerms ts)) (n.subst ts) := by
  unfold pairwiseBelow
  simp only [boundedSubst,coprimeBelowSubst,sucSubst,liftedFamilySubst]
  rfl

theorem residuesBelowRename {α β : Type} (t r : OTerm (α ⊕ Fin 1)) (c n : OTerm α) (j : α → β) :
    (residuesBelow t r c n).relabel j =
      residuesBelow (t.relabel (Sum.map j id)) (r.relabel (Sum.map j id)) (c.relabel j) (n.relabel j) := by
  unfold residuesBelow
  simp only [boundedRename,congruentRename,sucRelabel,Term.relabel_relabel,mapInl]

theorem residuesBelowSubst {α β : Type} (t r : OTerm (α ⊕ Fin 1)) (c n : OTerm α) (ts : α → OTerm β) :
    (residuesBelow t r c n).subst (fun x => emb (ts x)) =
      residuesBelow (t.subst (liftTerms ts)) (r.subst (liftTerms ts)) (c.subst ts) (n.subst ts) := by
  unfold residuesBelow
  simp only [boundedSubst,congruentSubst,sucSubst,liftSubst]

theorem solutionRename {α β : Type} (t r : OTerm (α ⊕ Fin 1)) (n : OTerm α) (j : α → β) :
    (InternalBoundedCRT.solution t r n).relabel j =
      InternalBoundedCRT.solution (t.relabel (Sum.map j id)) (r.relabel (Sum.map j id)) (n.relabel j) := by
  unfold InternalBoundedCRT.solution
  rw [existsRename,residuesBelowRename]
  simp only [familyLiftRename,Term.relabel_relabel,mapInl,varMap]

theorem solutionSubst {α β : Type} (t r : OTerm (α ⊕ Fin 1)) (n : OTerm α) (ts : α → OTerm β) :
    (InternalBoundedCRT.solution t r n).subst (fun x => emb (ts x)) =
      InternalBoundedCRT.solution (t.subst (liftTerms ts)) (r.subst (liftTerms ts)) (n.subst ts) := by
  unfold InternalBoundedCRT.solution
  rw [existsSubst,liftEmbedding,residuesBelowSubst]
  simp only [liftedFamilySubst,liftSubst]
  rfl

theorem pairwiseBelowInstantiate {α : Type} (t : OTerm (α ⊕ Fin 1)) (n : OTerm α) :
    instantiate (pairwiseBelow (t.relabel (Sum.map Sum.inl id)) (.var (.inr 0))) (emb n) =
      pairwiseBelow t n := by
  rw [instantiate,bindEmbedding,pairwiseBelowSubst,termLiftBind,varBind]

theorem solutionInstantiate {α : Type} (t r : OTerm (α ⊕ Fin 1)) (n : OTerm α) :
    instantiate (InternalBoundedCRT.solution (t.relabel (Sum.map Sum.inl id))
      (r.relabel (Sum.map Sum.inl id)) (.var (.inr 0))) (emb n) =
      InternalBoundedCRT.solution t r n := by
  rw [instantiate,bindEmbedding,solutionSubst,termLiftBind,termLiftBind,varBind]

theorem solutionMatrixInstantiate {α : Type} (t r : OTerm (α ⊕ Fin 1)) (n c : OTerm α) :
    instantiate (residuesBelow (t.relabel (Sum.map Sum.inl id))
      (r.relabel (Sum.map Sum.inl id)) (.var (.inr 0)) (n.relabel Sum.inl)) (emb c) =
      residuesBelow t r c n := by
  rw [instantiate,bindEmbedding,residuesBelowSubst,termLiftBind,termLiftBind,varBind,liftBind]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem solutionIntroduction (t r : OTerm (α ⊕ Fin 1)) (n c : OTerm α)
    (h : Nonempty (Derivation body Gamma (residuesBelow t r c n))) :
    Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r n)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb c)
  rw [solutionMatrixInstantiate]
  exact h

theorem solutionCases (Gamma : List (Formula α)) (t r : OTerm (α ⊕ Fin 1))
    (n : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (InternalBoundedCRT.solution t r n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (c : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (residuesBelow (t.relabel (Sum.map j id))
        (r.relabel (Sum.map j id)) c (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h hk⟩

theorem binarySolutionCases (Gamma : List (Formula α)) (a b r s : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (InternalBinaryCRT.solution a b r s)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (c : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (cf c (r.relabel j) (a.relabel j))) →
      Nonempty (Derivation body Delta (cf c (s.relabel j) (b.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let mat : Formula (α ⊕ Fin 1) := cf (.var (.inr 0)) (r.relabel Sum.inl) (a.relabel Sum.inl) ⊓
    cf (.var (.inr 0)) (s.relabel Sum.inl) (b.relabel Sum.inl)
  have hm : Derivation body (mat :: Gamma.map weaken) mat := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩
  exact ⟨Derivation.existentialElimination h hk⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCRTSyntaxProof
