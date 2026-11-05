module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryNormalizationProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingDiophantineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalProof
open Dioph Elementary BoundedUniversalTargets

/-- Reindex only the original free parameters. The witness and constraint
blocks are exactly those supplied by the checked natural-input normalizer. -/
theorem finiteParameterNormalization : FiniteParameterNormalization := by
  intro α _ S
  classical
  constructor
  · intro hS
    let e := Fintype.equivFin α
    let T : Set (Fin (Fintype.card α) → Nat) := {v | v ∘ e ∈ S}
    have hT : Dioph T := Dioph.reindex_dioph _ e hS
    obtain ⟨k,m,C,hC⟩ := ElementaryNormalizationProof.diophantineRepresented _ T hT
    refine ⟨k,m,fun j => (C j).rename e.symm id,?_⟩
    intro ν
    have hv : (ν ∘ e.symm) ∘ e = ν := by
      funext a
      simp [Function.comp_def]
    have hν : ν ∈ S ↔ ∃ w : Fin k → Nat, ∀ j : Fin m, (C j).Holds (ν ∘ e.symm) w := by
      simpa only [T,Set.mem_setOf_eq,hv] using hC (ν ∘ e.symm)
    refine hν.trans ?_
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨w,fun j => (ElementarySupportProof.renameHolds e.symm id (C j) ν w).2 (hw j)⟩
    · rintro ⟨w,hw⟩
      exact ⟨w,fun j => (ElementarySupportProof.renameHolds e.symm id (C j) ν w).1 (hw j)⟩
  · exact ElementaryNormalizationProof.representedDiophantine

/-- Normalize the original relation, then pack the variable number of its
existential elementary witness rows. No universal-closure premise is used. -/
theorem lengthBoundedUniversalClosure : LengthBoundedUniversalClosure := by
  intro n R hR
  obtain ⟨k,m,C,hC⟩ := (finiteParameterNormalization (Option (Fin n))
    {w | R (w none) (w ∘ some)}).1 hR
  have hrow (i : Nat) (ν : Fin n → Nat) :
      R i ν ↔ ∃ w : Fin k → Nat, ∀ j : Fin m, (C j).Holds (RowPacking.indexed i ν) w := by
    simpa only [Set.mem_setOf_eq,RowPacking.indexed,Function.comp_def] using
      hC (RowPacking.indexed i ν)
  apply (RowPackingDiophantineProof.pointwiseElementaryDiophantine n k m C).ext
  intro v
  change (∀ i, i < v none → ∃ w : Fin k → Nat,
    ∀ j : Fin m, (C j).Holds (RowPacking.indexed i (v ∘ some)) w) ↔
      ∀ i, i < v none → R i (v ∘ some)
  constructor
  · intro h i hi
    exact (hrow i (v ∘ some)).2 (h i hi)
  · intro h i hi
    exact (hrow i (v ∘ some)).1 (h i hi)

/-- Exact original variable-bound endpoint, with the supplied Diophantine
bound substituted into the length coordinate of the proved relation. -/
theorem variableBoundedUniversalClosure : CipherTargets.VariableBoundedUniversalClosure := by
  intro n bound R hbound hR
  exact Dioph.diophFn_comp1 (lengthBoundedUniversalClosure n R hR) hbound

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.BoundedUniversalProof
