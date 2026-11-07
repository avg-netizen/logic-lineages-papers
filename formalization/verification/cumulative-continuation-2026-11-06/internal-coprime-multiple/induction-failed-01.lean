module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBaseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalLeastNumberSyntaxProof InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof
open InternalCoprimeMultipleStepProof InternalCoprimeMultipleBaseProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalPositiveUnfoldingSupportProof
open InternalTermSubstitutionSyntaxProof InternalBetaBoundaryProof

theorem termLiftNext {α : Type} (t : OTerm (α ⊕ Fin 1)) :
    (t.relabel (Sum.map Sum.inl id)).subst (liftTerms nextTerm) = t.relabel (Sum.map Sum.inl id) := by
  rw [termRelabelSubst]
  have h : liftTerms nextTerm ∘ Sum.map Sum.inl id = Term.var ∘ Sum.map Sum.inl id := by
    funext x; cases x <;> rfl
  rw [h]
  exact (termRelabelAsSubst _ _).symm

/-- Genuine object-calculus induction: the index is the fresh object variable. -/
theorem actualBoundedCoprimeMultiple : InternalCoprimeMultipleTargets.ActualBoundedCoprimeMultiple := by
  intro body α m n t
  let M := (suc m).relabel (Sum.inl : α → α ⊕ Fin 1)
  let T := t.relabel (Sum.map Sum.inl id)
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := (coprimeBelow M T x).imp (commonMultiple M T x)
  have hb : Nonempty (Derivation body [] (instantiate theta (emb z))) := by
    simp only [theta,M,T,x,impInstantiate,coprimeBelowInstantiate,commonMultipleInstantiate]
    obtain ⟨hz⟩ := commonZero (body := body) (Gamma := [coprimeBelow (suc m) t z]) (suc m) t
    exact ⟨Derivation.implicationIntroduction hz⟩
  have hs : Nonempty (Derivation body [theta] (successorInstance theta)) := by
    simp only [theta,M,T,x,successorInstance,nextEmbedding,impSubst,
      coprimeBelowSubst,commonMultipleSubst,liftNext,termLiftNext,varNext]
    have hi : Derivation body (coprimeBelow M T (suc x) :: [theta]) theta :=
      Derivation.hypothesis (by simp)
    have ha : Derivation body (coprimeBelow M T (suc x) :: [theta]) (coprimeBelow M T (suc x)) :=
      Derivation.hypothesis List.mem_cons_self
    have hi' : Derivation body (coprimeBelow M T (suc x) :: [theta])
        ((coprimeBelow (suc (m.relabel Sum.inl)) T x).imp
          (commonMultiple (suc (m.relabel Sum.inl)) T x)) := by
      simpa only [theta,M,sucRelabel] using hi
    have ha' : Derivation body (coprimeBelow M T (suc x) :: [theta])
        (coprimeBelow (suc (m.relabel Sum.inl)) T (suc x)) := by
      simpa only [M,sucRelabel] using ha
    obtain ⟨h⟩ := multipleStep (m.relabel Sum.inl) T x ⟨hi'⟩ ⟨ha'⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨hb⟩ := hb
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb n) (natInduction theta hb hs)
  simpa only [theta,M,T,x,impInstantiate,coprimeBelowInstantiate,commonMultipleInstantiate] using
    (show Nonempty (Derivation body [] _) from ⟨h⟩)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleProof
