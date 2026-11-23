module

public import LogicLineages.NativeModule.PersistentMarking.TwoEnvironmentTargets
public import LogicLineages.NativeModule.PersistentMarking.RefinementSubstitutionSupport
public import LogicLineages.NativeModule.PersistentMarking.ExtendedEndpointProof
public import LogicLineages.NativeModule.PersistentMarking.ExtendedOpeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.TwoEnvironmentSupport
open Spine NameBridge RefinementSubstitutionSupport
abbrev Related := TwoEnvironmentTargets.Related

theorem leftValid {S : Signature} {γ δ : FreeMap} (h : Related S γ δ) : ∀ σ x, Valid S (γ σ x) := by
  intro σ x
  obtain ⟨hc⟩ := h σ x
  exact (ExtendedEndpointProof.weakFacts hc).1.2
theorem rightValid {S : Signature} {γ δ : FreeMap} (h : Related S γ δ) : ∀ σ x, Valid S (δ σ x) := by
  intro σ x
  obtain ⟨hc⟩ := h σ x
  exact (ExtendedEndpointProof.weakFacts hc).2.1.2

theorem maskRelated (S : Signature) (γ δ : FreeMap) (σ : Ty) (x : Nat) (h : Related S γ δ) :
    Related S (mask γ σ x) (mask δ σ x) := by
  intro τ y
  by_cases he : (τ,y) = (σ,x)
  · simp only [mask,he,if_true]; exact ⟨.var⟩
  · simpa only [mask,he,if_false] using h τ y

theorem annotation (θ : FreeMap) (ht : FreeMapTyped EmptyContext θ) (q : Expr) : (freeSub θ 0 q).type = q.type :=
  FreeCallProof.annotation θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (ht σ x)) 0 q

theorem mappedAt (θ : FreeMap) {xs i q} (h : At xs i q) : At (freeSubArgs θ 0 xs) i (freeSub θ 0 q) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem remove (θ : FreeMap) {xs q ys} (h : Remove xs q ys) : Remove (freeSubArgs θ 0 xs) (freeSub θ 0 q) (freeSubArgs θ 0 ys) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem mapSplit (θ : FreeMap) {xs ys zs} (h : Split xs ys zs) : Split (freeSubArgs θ 0 xs) (freeSubArgs θ 0 ys) (freeSubArgs θ 0 zs) := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

theorem nonempty (θ : FreeMap) (xs : Args) (h : Spine.Nonempty xs) : Spine.Nonempty (freeSubArgs θ 0 xs) := by
  cases xs with
  | nil => exact h
  | cons _ _ => trivial

theorem permutation (θ : FreeMap) {xs ys} (h : Permutation xs ys) : Permutation (freeSubArgs θ 0 xs) (freeSubArgs θ 0 ys) := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (remove θ hr) ih

theorem prefixMap (θ : FreeMap) {xs ys} (h : Prefix xs ys) : Prefix (freeSubArgs θ 0 xs) (freeSubArgs θ 0 ys) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem prefixCopy (θ : FreeMap) {f base extras τ q} (h : PrefixCopy f base extras τ q) :
    PrefixCopy f (freeSubArgs θ 0 base) (freeSubArgs θ 0 extras) τ (freeSub θ 0 q) := by
  cases h with
  | intro hp => exact .intro (prefixMap θ hp)

theorem prefixTuple (θ : FreeMap) {f base extras types qs} (h : PrefixTuple f base extras types qs) :
    PrefixTuple f (freeSubArgs θ 0 base) (freeSubArgs θ 0 extras) types (freeSubArgs θ 0 qs) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (prefixCopy θ h) ih

theorem prefixCopies (θ : FreeMap) (ht : FreeMapTyped EmptyContext θ) {f base extras qs} (h : PrefixCopies f base extras qs) :
    PrefixCopies f (freeSubArgs θ 0 base) (freeSubArgs θ 0 extras) (freeSubArgs θ 0 qs) := by
  induction h with
  | nil => exact .nil
  | @cons q qs h hs ih =>
    have hp := prefixCopy θ h
    rw [← annotation θ ht q] at hp
    exact .cons hp ih

theorem ownerCopies (θ : FreeMap) (f : Head) (base extras : Args) (types : List Ty) :
    freeSubArgs θ 0 (Spine.ownerCopies f base extras types) = Spine.ownerCopies f (freeSubArgs θ 0 base) (freeSubArgs θ 0 extras) types := by
  induction types with
  | nil => rfl
  | cons σ types ih => simp only [Spine.ownerCopies,freeSubArgs,freeSub,ih]

theorem call (θ : FreeMap) (ht : FreeMapTyped EmptyContext θ) {q args r} (h : apply q args = some r) :
    apply (freeSub θ 0 q) (freeSubArgs θ 0 args) = some (freeSub θ 0 r) := by
  cases args with
  | nil => simp only [apply,Option.some.injEq] at h; subst r; rfl
  | cons a rest => exact FreeCallProof.aux θ (fun σ x => SpineShiftProof.annotationExact _ _ _ (ht σ x)) q (.cons a rest) .nil r h

def Result (S : Signature) (γ δ : FreeMap) : ExtendedJudgment → Prop
  | .weak s t => ExtendedWeak S (freeSub γ 0 s) (freeSub δ 0 t)
  | .strict s t => ExtendedStrict S (freeSub γ 0 s) (freeSub δ 0 t)
  | .matching ss ts => _root_.Nonempty (ExtendedMatchingTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
  | .multiset ss ts => _root_.Nonempty (ExtendedMultisetTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
  | .coverage ss ts => _root_.Nonempty (ExtendedCoverageTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))
  | .whole f base extras ts => _root_.Nonempty (ExtendedWholeTree S f (freeSubArgs γ 0 base) (freeSubArgs γ 0 extras) (freeSubArgs δ 0 ts))
  | .ordered ss ts => _root_.Nonempty (ExtendedOrderedTree S (freeSubArgs γ 0 ss) (freeSubArgs δ 0 ts))

def Smaller (S : Signature) (n : Nat) : Prop := ∀ j (h : ExtendedTree S j), ExtendedMeasure.treeSize h < n →
  ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ j
end LogicLineages.PersistentMarking.TwoEnvironmentSupport
