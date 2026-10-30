module

public import LogicLineages.ModelsAlgebra.Forests.AgeApplicationTargets
public import LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof

/-! Empty-carrier conventions and actual hereditary forbidden classes. The
finite code check has a separate uniform primitive-recursive certificate. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof

open AgeConstruction AgeNecessaryProof AgeCompletionProof

private def emptyForest : FiniteOrderForest where
  Carrier := Fin 0
  carrierFintype := inferInstance
  carrierPartialOrder := inferInstance
  forest := by intro x; exact Fin.elim0 x

private noncomputable def emptyEmbedding (α : Type) [PartialOrder α] : emptyForest.Carrier ↪o α where
  toFun := fun x => Fin.elim0 x
  inj' := fun x => Fin.elim0 x
  map_rel_iff' := by intro x; exact Fin.elim0 x

theorem realizedForestAgeNonempty : Targets.RealizedForestAgeNonempty := by
  intro K A hAge
  exact ⟨emptyForest, (hAge emptyForest).mpr ⟨emptyEmbedding A.Carrier⟩⟩

theorem avoidanceClassHereditary : Targets.AvoidanceClassHereditary := by
  rintro U F G hF ⟨e⟩ B hB ⟨f⟩
  exact hF B hB ⟨f.comp e⟩

theorem avoidanceClassNonemptyCriterion : Targets.AvoidanceClassNonemptyCriterion := by
  classical
  intro U
  constructor
  · rintro ⟨F, hF⟩ B hB
    by_contra hempty
    letI : IsEmpty B.Carrier := ⟨fun b => hempty ⟨b⟩⟩
    let e : B.Carrier ↪o F.Carrier := {
      toFun := fun x => isEmptyElim x
      inj' := fun x => isEmptyElim x
      map_rel_iff' := by intro x; exact isEmptyElim x }
    exact hF B hB ⟨e⟩
  · intro h
    refine ⟨emptyForest, ?_⟩
    rintro B hB ⟨e⟩
    obtain ⟨b⟩ := h B hB
    exact Fin.elim0 (e b)

theorem noEmptyCodeTestCorrect : Targets.NoEmptyCodeTestCorrect := by
  intro U hU
  simp only [noEmptyTest, decide_eq_true_eq]
  rw [avoidanceClassNonemptyCriterion]
  constructor
  · intro h B hB
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hB
    change Nonempty (Fin c.val.1)
    exact ⟨⟨0, h c.val c.property⟩⟩
  · intro h c hc
    have hb := h (FiniteCode.toForest c (hU c hc))
      (List.mem_map.mpr ⟨⟨c, hc⟩, by simp, rfl⟩)
    change Nonempty (Fin c.1) at hb
    obtain ⟨i⟩ := hb
    exact Nat.zero_lt_of_lt i.isLt

theorem noEmptyCodeTestPrimitiveRecursive : Targets.NoEmptyCodeTestPrimitiveRecursive := by
  have h : PrimrecPred (fun c : FiniteCode.Code => 0 < c.1) :=
    Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst
  exact h.forall_mem_list.decide

theorem forbiddenForestAgeCriterion : Targets.ForbiddenForestAgeCriterion := by
  intro U
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨realizedForestAgeHasJEP _ A hA,
      (avoidanceClassNonemptyCriterion U).mp (realizedForestAgeNonempty _ A hA)⟩
  · rintro ⟨hj, hn⟩
    exact (fullForestAgeRealization (AvoidanceClass U)
      ((avoidanceClassNonemptyCriterion U).mpr hn) (avoidanceClassHereditary U)).mpr hj

end LogicLineages.ModelsAlgebra.Forests.AgeApplicationProof
