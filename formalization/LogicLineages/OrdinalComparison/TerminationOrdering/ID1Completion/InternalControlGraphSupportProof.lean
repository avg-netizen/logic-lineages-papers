module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalRecursionClosureProof InternalRecursionClosureLogicProof InternalRecursionFreeInitialProof
open InternalGraphCompositionSyntaxProof InternalGraphCompositionIntroductionProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraph InternalRecursionGraphStepSyntaxProof
open InternalRecursionGraphZeroIntroductionProof InternalRecursionGraphSuccessorIntroductionProof
open InternalTagArithmeticSyntaxProof (emb z suc eqn eqnRelabel zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open InternalBetaTotalityProof InternalQuotientComparisonProof
open InternalLinearCombinationZeroRemainderProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

@[simp] theorem equalEqn (s t : OrdinaryArithmetic.Term α) : equal s t = eqn s t := by
  exact onEquality _ _ _

@[simp] theorem programRename {n : Nat} {β : Type} (p : Program n)
    (out : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α) (j : α → β) :
    (programGraph p out xs).relabel j =
      programGraph p (out.relabel j) (fun i => (xs i).relabel j) :=
  graphRename _ _ _ _

theorem emptyRename {β : Type} (j : α → β) :
    (fun i : Fin 0 => (Fin.elim0 i : OrdinaryArithmetic.Term α).relabel j) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

theorem zeroValue (xs : Fin 0 → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph .zero z xs)) := by
  unfold programGraph
  rw [actualInitialGraphInstances.1,onEquality]
  exact ⟨refl z⟩

theorem successorValue (xs : Fin 1 → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph .succ (suc (xs 0)) xs)) := by
  unfold programGraph
  rw [actualInitialGraphInstances.2.1,onEquality]
  exact ⟨refl _⟩

theorem projectionValue {n : Nat} (i : Fin n) (xs : Fin n → OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (programGraph (.projection i) (xs i) xs)) := by
  unfold programGraph
  rw [actualInitialGraphInstances.2.2,onEquality]
  exact ⟨refl _⟩

theorem compositionValue {m n : Nat} (f : Program n) (g : Fin n → Program m)
    (out : OrdinaryArithmetic.Term α) (xs : Fin m → OrdinaryArithmetic.Term α)
    (ys : Fin n → OrdinaryArithmetic.Term α)
    (hf : Nonempty (Derivation body Gamma (programGraph f out ys)))
    (hg : ∀ i, Nonempty (Derivation body Gamma (programGraph (g i) (ys i) xs))) :
    Nonempty (Derivation body Gamma (programGraph (.composition f g) out xs)) :=
  actualOriginalCompositionIntroduction body m n α Gamma _ _ out xs ys hf hg

theorem recursionZeroValue {n : Nat} (f : Program n) (g : Program (n+2))
    (out : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hf : Nonempty (Derivation body Gamma (programGraph f out xs))) :
    Nonempty (Derivation body Gamma (programGraph (.recursion f g) out (Fin.cons z xs))) :=
  closedApply (actualOriginalRecursionZeroIntroduction body n α _ _ out xs) hf

/-- Previous-result existence is supplied by the proved original Program
closure. The successor step is still the literal source AST graph. -/
theorem recursionSuccessorValue {n : Nat} (f : Program n) (g : Program (n+2))
    (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hg : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OrdinaryArithmetic.Term β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph g (out.relabel j)
        (Fin.cons (t.relabel j) (Fin.cons v (fun i => (xs i).relabel j)))))) :
    Nonempty (Derivation body Gamma (programGraph (.recursion f g) out (Fin.cons (suc t) xs))) := by
  obtain ⟨ht⟩ := (actualOriginalPrograms body (n+1) (.recursion f g)).1 α (Fin.cons t xs)
  apply graphExistsCases Gamma (OrdinaryArithmetic.graphFormula (.recursion f g))
    (Fin.cons t xs) _ ⟨weakenClosed ht Gamma⟩
  intro β j Delta v hj hv
  simp only [programRename,consTermRename,sucRelabel]
  have hv' : Nonempty (Derivation body Delta (recursion
      (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g) v
      (t.relabel j) (fun i => (xs i).relabel j))) := by
    simpa only [consTermRename,OrdinaryArithmetic.graphFormula,InternalRecursionGraph.recursion] using hv
  exact recursionSuccessorIntroduction Delta _ _ (out.relabel j) (t.relabel j) v
    (fun i => (xs i).relabel j) hv' (hg β j Delta v hj)

theorem outputTransport {n : Nat} (p : Program n) (out other : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (hp : Nonempty (Derivation body Gamma (programGraph p out xs))) :
    Nonempty (Derivation body Gamma (programGraph p other xs)) :=
  graphOutputTransport Gamma _ out other xs he hp

theorem headTransport {n : Nat} (p : Program (n+1))
    (out s t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (he : Nonempty (Derivation body Gamma (eqn s t)))
    (hp : Nonempty (Derivation body Gamma (programGraph p out (Fin.cons s xs)))) :
    Nonempty (Derivation body Gamma (programGraph p out (Fin.cons t xs))) := by
  apply graphInputTransport body α (n+1) Gamma _ out (Fin.cons s xs) (Fin.cons t xs) _ hp
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [onEquality]
    exact he
  · rw [onEquality]
    exact ⟨refl _⟩

theorem valueUnique {n : Nat} (p : Program n) (out other : OrdinaryArithmetic.Term α)
    (xs : Fin n → OrdinaryArithmetic.Term α)
    (hp : Nonempty (Derivation body Gamma (programGraph p out xs)))
    (hq : Nonempty (Derivation body Gamma (programGraph p other xs))) :
    Nonempty (Derivation body Gamma (eqn out other)) := by
  have h := functionalApply _ (actualOriginalPrograms body n p).2 Gamma out other xs hp hq
  rw [onEquality] at h
  exact h

/-- The already-derived original arithmetic split supplies the arbitrary
predecessor witness; no standard-natural semantic case split is used. -/
theorem zeroSuccessorCases (Gamma : List (Formula α)) (t : OrdinaryArithmetic.Term α) (psi : Formula α)
    (hz : Nonempty (Derivation body (eqn t z :: Gamma) psi))
    (hs : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OrdinaryArithmetic.Term β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (eqn (t.relabel j) (suc v))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨hz⟩ := hz
  have hs' : Nonempty (Derivation body (successorExists t :: Gamma) psi) := by
    apply InternalLinearCombinationZeroRemainderProof.successorCases
      (successorExists t :: Gamma) t psi ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta v hj he
    exact hs β j Delta v (fun p hp => hj p (List.mem_cons_of_mem _ hp)) he
  obtain ⟨hs'⟩ := hs'
  exact ⟨disjunctionElimination (zeroOrSuccessor t)
    (Derivation.implicationIntroduction hz) (Derivation.implicationIntroduction hs')⟩

theorem nonzeroValue {n : Nat} (p : Program (n+1))
    (out t : OrdinaryArithmetic.Term α) (xs : Fin n → OrdinaryArithmetic.Term α)
    (hn : Nonempty (Derivation body Gamma (eqn t z).not))
    (hs : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OrdinaryArithmetic.Term β),
      Nonempty (Derivation body Delta (programGraph p (out.relabel j)
        (Fin.cons (suc v) (fun i => (xs i).relabel j))))) :
    Nonempty (Derivation body Gamma (programGraph p out (Fin.cons t xs))) := by
  obtain ⟨hn⟩ := hn
  apply zeroSuccessorCases Gamma t _
  · exact ⟨Derivation.explosion (Derivation.implicationElimination
      (addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro β j Delta v _ ⟨he⟩
    simp only [programRename,consTermRename]
    exact headTransport p (out.relabel j) (suc v) (t.relabel j)
      (fun i => (xs i).relabel j) ⟨symm he⟩ (hs β j Delta v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
