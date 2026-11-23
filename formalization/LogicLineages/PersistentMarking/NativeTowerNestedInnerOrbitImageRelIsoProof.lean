import LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitReflectionProof
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Basic

namespace LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitImageRelIsoProof
open Spine NativeIteratorStrictTargets
open NativeTowerOuterIndexConeProof NativeTowerNestedInnerOrbitLexProof NativeTowerNestedInnerOrbitReflectionProof
open NativeTowerWitnessFamilyProof

theorem exact_OriginalOrbitLexWellOrder (k : Nat) : IsWellOrder (OrbitCoords k) (OrbitLex k) := by
  induction k with
  | zero =>
    change IsWellOrder Nat Nat.lt
    exact { wf := Nat.lt_wfRel.wf
            trichotomous := fun a b hab hba => ((Nat.lt_trichotomy a b).resolve_left hab).resolve_right hba }
  | succ k ih =>
    letI := ih
    letI : IsWellOrder Nat Nat.lt :=
      { wf := Nat.lt_wfRel.wf
        trichotomous := fun a b hab hba => ((Nat.lt_trichotomy a b).resolve_left hab).resolve_right hba }
    have matchLex : OrbitLex (k+1) = Prod.Lex (OrbitLex k) Nat.lt := by
      funext p q
      exact propext Prod.lex_def.symm
    rw [matchLex]
    exact (inferInstance : IsWellOrder (OrbitCoords k × Nat) (Prod.Lex (OrbitLex k) Nat.lt))

/-- Actual closed native image, not a copy of its index type with an imposed order. -/
abbrev Image (S : Signature) (l k : Nat) := ↥(Set.range (nestedPoint S l k))

def imageStrict (S : Signature) (l k : Nat) : Image S l k → Image S l k → Prop :=
  fun a b => NativeBelow a.val b.val

noncomputable def actualImageIso (S : Signature) (l k : Nat) :
    OrbitLex k ≃r imageStrict S l k where
  toEquiv := Equiv.ofInjective (nestedPoint S l k)
    (fun {_ _} eq => exact_ActualFixedTowerNestedInjective S l k _ _ eq)
  map_rel_iff' := by
    intro p q
    change NativeBelow (nestedPoint S l k p) (nestedPoint S l k q) ↔ OrbitLex k p q
    exact exact_ActualFixedTowerNestedStrictIff S l k p q

theorem exact_ActualFixedTowerImageRelIsoAndBound (S : Signature) (l k : Nat) :
    ∃ e : OrbitLex k ≃r imageStrict S l k,
      (∀ p, (e p).val = nestedPoint S l k p) ∧
      (∀ p : Image S l k, NativeBelow p.val (closedTower S (l+2))) := by
  refine ⟨actualImageIso S l k,fun _ => rfl,?_⟩
  rintro ⟨value,⟨p,rfl⟩⟩
  exact (exact_ActualFixedTowerNestedLex S l k).1 p

theorem exact_ActualFixedTowerImageWellOrder (S : Signature) (l k : Nat) :
    IsWellOrder (Image S l k) (imageStrict S l k) := by
  letI := exact_OriginalOrbitLexWellOrder k
  exact (actualImageIso S l k).symm.toRelEmbedding.isWellOrder

#print axioms exact_OriginalOrbitLexWellOrder
#print axioms exact_ActualFixedTowerImageRelIsoAndBound
#print axioms exact_ActualFixedTowerImageWellOrder

end LogicLineages.PersistentMarking.NativeTowerNestedInnerOrbitImageRelIsoProof
