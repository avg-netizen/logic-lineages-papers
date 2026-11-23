import LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapLexReflectionProof
import Mathlib.Logic.Equiv.Set
import Mathlib.Order.RelIso.Basic

namespace LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapImageRelIsoProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalCapPathsTargets NativeOrdinalRepeatedCapLexEmbeddingProof
open NativeOrdinalRepeatedCapLexReflectionProof

/-- The actual subtype of closed native image terms, not an index copy. -/
abbrev BlockImageRange (S : Signature) (u : ClosedNativeTerm S indexType) :=
  ↥(Set.range (blockImage S u))

def actualImageStrict (S : Signature) (u : ClosedNativeTerm S indexType) :
    BlockImageRange S u → BlockImageRange S u → Prop :=
  fun x y => NativeBelow x.val y.val

abbrev natLex : (Nat × Nat) → (Nat × Nat) → Prop :=
  Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)

noncomputable def actualBlockImageIso (S : Signature) (u : ClosedNativeTerm S indexType) :
    natLex ≃r actualImageStrict S u where
  toEquiv := Equiv.ofInjective (blockImage S u) (exact_ActualNativeBlockImageInjective S u)
  map_rel_iff' := by
    intro p q
    change NativeBelow (blockImage S u p) (blockImage S u q) ↔ natLex p q
    rw [exact_ActualNativeBlockStrictIff]
    simp only [BlockLex,Prod.lex_def]

/-- The forward map is the literal native term already used for each pair. -/
theorem exact_ActualBlockImageRelIso (S : Signature) (u : ClosedNativeTerm S indexType) :
    ∃ e : natLex ≃r actualImageStrict S u, ∀ p, (e p).val = blockImage S u p :=
  ⟨actualBlockImageIso S u, fun _ => rfl⟩

/-- The well-order is for this actual restriction of NativeBelow only. -/
theorem exact_ActualBlockImageWellOrder (S : Signature) (u : ClosedNativeTerm S indexType) :
    IsWellOrder (BlockImageRange S u) (actualImageStrict S u) := by
  letI : IsWellOrder Nat (fun x y : Nat => x < y) :=
    { wf := Nat.lt_wfRel.wf
      trichotomous := by
        intro a b hab hba
        exact ((Nat.lt_trichotomy a b).resolve_left hab).resolve_right hba }
  exact (actualBlockImageIso S u).symm.toRelEmbedding.isWellOrder

#print axioms exact_ActualBlockImageRelIso
#print axioms exact_ActualBlockImageWellOrder

end LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapImageRelIsoProof
