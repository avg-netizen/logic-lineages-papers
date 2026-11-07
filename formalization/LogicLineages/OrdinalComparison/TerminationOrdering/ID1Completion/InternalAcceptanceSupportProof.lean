module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open InternalControlGraphSupportProof InternalRecursionClosureProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Original Program totality eliminates an object-language witness, never a semantic value. -/
theorem programCases {n : Nat} (p : Program n) (xs : Fin n → OTerm α) (psi : Formula α)
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph p v (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨ht⟩ := (actualOriginalPrograms body n p).1 α xs
  exact graphExistsCases Gamma _ xs psi ⟨weakenClosed ht Gamma⟩ k

theorem programCompositionCases {m n : Nat} (f : Program n) (g : Fin n → Program m)
    (out : OTerm α) (xs : Fin m → OTerm α) (psi : Formula α)
    (d : Nonempty (Derivation body Gamma (programGraph (.composition f g) out xs)))
    (h : ∀ (β : Type) (j : α → β) (ys : Fin n → OTerm β) (Delta : List (Formula β)),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (programGraph f (out.relabel j) ys)) →
      (∀ i, Nonempty (Derivation body Delta (programGraph (g i) (ys i)
        (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) :=
  compositionCases Gamma _ _ out xs psi d h

/-- Recover the outer graph at known component outputs; all witnesses are internal. -/
theorem compositionRecover {m n : Nat} (f : Program n) (g : Fin n → Program m)
    (out : OTerm α) (xs : Fin m → OTerm α) (ys : Fin n → OTerm α)
    (hw : Nonempty (Derivation body Gamma (programGraph (.composition f g) out xs)))
    (hg : ∀ i, Nonempty (Derivation body Gamma (programGraph (g i) (ys i) xs))) :
    Nonempty (Derivation body Gamma (programGraph f out ys)) := by
  apply programCases f ys _
  intro β j Delta v hj hv
  simp only [programRename]
  have hw' := renameInto hw j Delta hj
  simp only [programRename] at hw'
  have hg' (i : Fin n) := renameInto (hg i) j Delta hj
  simp only [programRename] at hg'
  have hs := compositionValue f g v (fun i => (xs i).relabel j)
    (fun i => (ys i).relabel j) hv hg'
  obtain ⟨he⟩ := valueUnique (.composition f g) (out.relabel j) v
    (fun i => (xs i).relabel j) hw' hs
  exact outputTransport f v (out.relabel j) (fun i => (ys i).relabel j)
    ⟨InternalTagArithmeticSupportProof.symm he⟩ hv

theorem oneTuple {X : Type} (ys : Fin 1 → X) : Fin.cons (ys 0) Fin.elim0 = ys := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem threeTuple {X : Type} (ys : Fin 3 → X) :
    Fin.cons (ys 0) (Fin.cons (ys 1) (Fin.cons (ys 2) Fin.elim0)) = ys := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
      rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
