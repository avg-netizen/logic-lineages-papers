module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureFunctionalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalRecursionClosure InternalRecursionClosureSyntaxProof
open InternalRecursionClosureLogicProof InternalGraphCompositionSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalRecursionGraphSyntaxProof InternalRecursionGraphStepSyntaxProof InternalClosedProgramsBindingProof
open InternalRecursionGraphZeroEliminationProof InternalRecursionGraphSuccessorEliminationProof
open InternalPositiveUnfoldingSupportProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (natInduction)

variable {body : Positive (Fin 1)} {α : Type} {n : Nat}

theorem zeroFunctionalCore (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hf : Functional body f) (Gamma : List (Formula α))
    (out other : OTerm α) (xs : Fin n → OTerm α)
    (d : Nonempty (Derivation body Gamma (recursion f g out z xs)))
    (e : Nonempty (Derivation body Gamma (recursion f g other z xs))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (out.equal other))) := by
  exact functionalApply f hf Gamma out other xs
    (closedApply (actualOriginalRecursionZeroElimination body n α f g out xs) d)
    (closedApply (actualOriginalRecursionZeroElimination body n α f g other xs) e)

/-- The only induction input is universal at-most-one at the predecessor.
No existence premise is used. Equal predecessor values transport g's inputs. -/
theorem successorFunctionalCore (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hg : Functional body g) (Gamma : List (Formula α))
    (out other t : OTerm α) (xs : Fin n → OTerm α)
    (hu : Nonempty (Derivation body Gamma (uniqueAt f g t xs)))
    (d : Nonempty (Derivation body Gamma (recursion f g out (suc t) xs)))
    (e : Nonempty (Derivation body Gamma (recursion f g other (suc t) xs))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (out.equal other))) := by
  have ds := closedApply (actualOriginalRecursionSuccessorElimination body n α f g out t xs) d
  apply successorCases Gamma f g out t xs _ ds
  intro β j Delta v hj dv dg
  rw [equalityRename]
  have eu := renameInto hu j Delta hj
  rw [uniqueAtRename] at eu
  have er := renameInto e j Delta hj
  rw [recursionRename,sucRelabel] at er
  have es := closedApply (actualOriginalRecursionSuccessorElimination body n β f g
    (other.relabel j) (t.relabel j) (fun i => (xs i).relabel j)) er
  apply successorCases Delta f g (other.relabel j) (t.relabel j)
    (fun i => (xs i).relabel j) _ es
  intro γ l Theta w hl ev eg
  rw [equalityRename]
  have hu' := renameInto eu l Theta hl
  rw [uniqueAtRename] at hu'
  have dv' := renameInto dv l Theta hl
  rw [recursionRename] at dv'
  have dg' := renameInto dg l Theta hl
  rw [graphRename,consTermRename,consTermRename] at dg'
  have heq := uniqueApply f g (v.relabel l) w ((t.relabel j).relabel l)
    (fun i => ((xs i).relabel j).relabel l) hu' dv' ev
  have deq : ∀ i : Fin (n+2), Nonempty (Derivation body Theta
      (arithmeticEmbedding.onFormula
        ((Fin.cons (α := fun _ => OTerm γ) ((t.relabel j).relabel l) (Fin.cons (v.relabel l)
          (fun a => ((xs a).relabel j).relabel l)) i).equal
        ((Fin.cons (α := fun _ => OTerm γ) ((t.relabel j).relabel l) (Fin.cons w
          (fun a => ((xs a).relabel j).relabel l))) i)))) := by
    intro i
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun a => ?_) k) i
    · rw [onEquality]
      exact ⟨Derivation.equalityReflexivity _⟩
    · exact heq
    · rw [onEquality]
      exact ⟨Derivation.equalityReflexivity _⟩
  have transported := graphInputTransport body γ (n+2) Theta g ((out.relabel j).relabel l)
    _ _ deq dg'
  exact functionalApply g hg Theta ((out.relabel j).relabel l) ((other.relabel j).relabel l)
    (Fin.cons ((t.relabel j).relabel l) (Fin.cons w (fun a => ((xs a).relabel j).relabel l)))
    transported eg

theorem uniqueZero (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hf : Functional body f) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body [] (uniqueAt f g z xs)) := by
  unfold uniqueAt
  apply actualFiniteUniversalIntroduction body α 2 []
  simp only [zRelabel,List.map_nil]
  let A := recursion f g (.var (.inr (0 : Fin 2))) z (fun i => (xs i).relabel Sum.inl) ⊓
    recursion f g (.var (.inr 1)) z (fun i => (xs i).relabel Sum.inl)
  obtain ⟨d⟩ := zeroFunctionalCore f g hf [A] (.var (.inr 0)) (.var (.inr 1))
    (fun i => (xs i).relabel Sum.inl)
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem uniqueSuccessor (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hg : Functional body g) (Gamma : List (Formula α)) (t : OTerm α) (xs : Fin n → OTerm α)
    (hu : Nonempty (Derivation body Gamma (uniqueAt f g t xs))) :
    Nonempty (Derivation body Gamma (uniqueAt f g (suc t) xs)) := by
  unfold uniqueAt
  apply actualFiniteUniversalIntroduction body α 2 Gamma
  simp only [sucRelabel]
  let A := recursion f g (.var (.inr (0 : Fin 2))) (suc (t.relabel Sum.inl))
      (fun i => (xs i).relabel Sum.inl) ⊓
    recursion f g (.var (.inr 1)) (suc (t.relabel Sum.inl)) (fun i => (xs i).relabel Sum.inl)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 2))
  have hu' := renameInto hu Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [uniqueAtRename] at hu'
  obtain ⟨d⟩ := successorFunctionalCore f g hg Delta (.var (.inr 0)) (.var (.inr 1))
    (t.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl) hu'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Original PA induction, with both compared outputs universally bound
inside the expanded formula. -/
theorem uniqueAll (f : OFormula (Fin (n+1))) (g : OFormula (Fin (n+3)))
    (hf : Functional body f) (hg : Functional body g) (t : OTerm α) (xs : Fin n → OTerm α) :
    Nonempty (Derivation body [] (uniqueAt f g t xs)) := by
  let theta := uniqueAt f g (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)
  have base : Derivation body [] (instantiate theta (emb z)) := by
    change Derivation body [] (instantiate (uniqueAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)) (emb z))
    rw [uniqueAtInstantiate]
    exact Classical.choice (uniqueZero f g hf xs)
  have step : Derivation body [theta] (successorInstance theta) := by
    change Derivation body [theta] (successorInstance (uniqueAt f g (.var (.inr (0 : Fin 1)))
      (fun i => (xs i).relabel Sum.inl)))
    rw [uniqueAtSuccessor]
    exact Classical.choice (uniqueSuccessor f g hg [theta] (.var (.inr 0))
      (fun i => (xs i).relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have all := natInduction theta base (by simpa only [List.map_nil] using step)
  have result := Derivation.universalElimination (emb t) all
  change Derivation body [] (instantiate (uniqueAt f g (.var (.inr (0 : Fin 1)))
    (fun i => (xs i).relabel Sum.inl)) (emb t)) at result
  rw [uniqueAtInstantiate] at result
  exact ⟨result⟩

theorem actualOriginalRecursionFunctionality :
    InternalRecursionClosureTargets.ActualOriginalRecursionFunctionality := by
  intro body n f g hf hg α out other ys
  have split : Fin.cons (ys 0) (fun i => ys i.succ) = ys := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  let A := graph (OrdinaryArithmetic.recursionGraph f g) out ys ⊓
    graph (OrdinaryArithmetic.recursionGraph f g) other ys
  obtain ⟨u⟩ := uniqueAll f g hf hg (ys 0) (fun i => ys i.succ)
  have d : Nonempty (Derivation body [A] (recursion f g out (ys 0) (fun i => ys i.succ))) := by
    unfold recursion
    rw [split]
    exact ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have e : Nonempty (Derivation body [A] (recursion f g other (ys 0) (fun i => ys i.succ))) := by
    unfold recursion
    rw [split]
    exact ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨r⟩ := uniqueApply f g out other (ys 0) (fun i => ys i.succ)
    ⟨weakenClosed u [A]⟩ d e
  exact ⟨Derivation.implicationIntroduction r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureFunctionalityProof
