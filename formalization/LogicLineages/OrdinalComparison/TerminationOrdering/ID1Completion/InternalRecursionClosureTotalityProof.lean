module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTotalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalRecursionClosure InternalRecursionClosureSyntaxProof
open InternalRecursionClosureLogicProof InternalGraphCompositionSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalRecursionGraphZeroIntroductionProof InternalRecursionGraphSuccessorIntroductionProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (natInduction)

variable {body : Positive (Fin 1)} {α : Type} {n : Nat}

theorem totalZero (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hf : Total body f) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body [] (totalAt f g z xs)) := by
  apply graphExistsCases [] f xs _ (hf α xs)
  intro β j Delta out _ hout
  rw [totalAtRename,zRelabel]
  apply totalIntroduction f g out z (fun i => (xs i).relabel j)
  exact closedApply (actualOriginalRecursionZeroIntroduction body n β f g out
    (fun i => (xs i).relabel j)) hout

theorem totalSuccessor (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hg : Total body g) (Gamma : List (Formula α)) (t : OTerm α) (xs : Fin n → OTerm α)
    (h : Nonempty (Derivation body Gamma (totalAt f g t xs))) :
    Nonempty (Derivation body Gamma (totalAt f g (suc t) xs)) := by
  apply totalCases Gamma f g t xs _ h
  intro β j Delta old _ hold
  rw [totalAtRename,sucRelabel]
  obtain ⟨dg⟩ := hg β (Fin.cons (t.relabel j) (Fin.cons old (fun i => (xs i).relabel j)))
  apply graphExistsCases Delta g (Fin.cons (t.relabel j) (Fin.cons old
    (fun i => (xs i).relabel j))) _ ⟨weakenClosed dg Delta⟩
  intro γ l Theta out hl hout
  rw [totalAtRename,sucRelabel]
  have hr := renameInto hold l Theta hl
  rw [recursionRename] at hr
  simp only [consTermRename] at hout
  apply totalIntroduction f g out (suc ((t.relabel j).relabel l))
    (fun i => ((xs i).relabel j).relabel l)
  exact recursionSuccessorIntroduction Theta f g out ((t.relabel j).relabel l) (old.relabel l)
    (fun i => ((xs i).relabel j).relabel l) hr hout

/-- Original PA induction on existential output, at every object-language
counter and every tuple of parameter terms. -/
theorem totalAll (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hf : Total body f) (hg : Total body g) (t : OTerm α) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body [] (totalAt f g t xs)) := by
  let theta := totalAt f g (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)
  have base : Derivation body [] (instantiate theta (emb z)) := by
    change Derivation body [] (instantiate (totalAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) (emb z))
    rw [totalAtInstantiate]
    exact Classical.choice (totalZero f g hf xs)
  have step : Derivation body [theta] (successorInstance theta) := by
    change Derivation body [theta] (successorInstance (totalAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)))
    rw [totalAtSuccessor]
    exact Classical.choice (totalSuccessor f g hg [theta] (.var (.inr 0))
      (fun i => (xs i).relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have all := natInduction theta base (by simpa only [List.map_nil] using step)
  have result := Derivation.universalElimination (emb t) all
  change Derivation body [] (instantiate (totalAt f g (.var (.inr (0 : Fin 1)))
    (fun i => (xs i).relabel Sum.inl)) (emb t)) at result
  rw [totalAtInstantiate] at result
  exact ⟨result⟩

theorem actualOriginalRecursionTotality : InternalRecursionClosureTargets.ActualOriginalRecursionTotality := by
  intro body n f g hf hg α ys
  have h := totalAll f g hf hg (ys 0) (fun i => ys i.succ)
  unfold totalAt recursion at h
  have split : Fin.cons ((ys 0).relabel (Sum.inl : α → α ⊕ Fin 1))
      (fun i => (ys i.succ).relabel Sum.inl) = (fun i => (ys i).relabel Sum.inl) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [split] at h
  exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureTotalityProof
