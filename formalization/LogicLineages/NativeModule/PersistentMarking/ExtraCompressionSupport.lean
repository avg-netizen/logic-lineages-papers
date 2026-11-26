module

public import LogicLineages.NativeModule.PersistentMarking.ExtraCompressionTargets
public import LogicLineages.NativeModule.PersistentMarking.ConservativeOwnerSupport

@[expose] public section

namespace LogicLineages.PersistentMarking.ExtraCompressionSupport
open Spine AuxiliaryReflexivityProof ConservativeOwnerSupport

def copies (f : Head) (base extras : Args) : Args → Args
  | .nil => .nil
  | .cons q qs => .cons (.marked f q.type base extras) (copies f base extras qs)

theorem copiesPrefix (f : Head) (base extras qs : Args) :
    PrefixCopies f base extras (copies f base extras qs) := by
  cases qs with
  | nil => exact .nil
  | cons q qs => exact .cons (.intro (prefixRefl extras)) (copiesPrefix f base extras qs)
termination_by sizeOf qs

theorem ordered {S : Signature} {f : Head} {base extras qs : Args}
    (h : ExtendedWholeTree S f base extras qs) :
    _root_.Nonempty (ExtendedOrderedTree S (copies f base extras qs) qs) := by
  cases qs with
  | nil => exact ⟨.orderedNil⟩
  | cons q qs =>
    cases h with
    | wholeCons hw hs =>
      obtain ⟨hs'⟩ := ordered hs
      exact ⟨.orderedCons hw hs'⟩
termination_by sizeOf qs

theorem removeAfter (xs : Args) (q : Expr) (ys : Args) :
    Remove (xs.append (.cons q ys)) q (xs.append ys) := by
  cases xs with
  | nil => exact .here
  | cons x xs => exact .there (removeAfter xs q ys)
termination_by sizeOf xs

theorem permutationRefl (xs : Args) : Permutation xs xs := by
  cases xs with
  | nil => exact .nil
  | cons x xs => exact .cons .here (permutationRefl xs)
termination_by sizeOf xs

theorem permutationBlocks (xs ys : Args) : Permutation (xs.append ys) (ys.append xs) := by
  cases xs with
  | nil =>
    rw [appendNil]
    exact permutationRefl ys
  | cons x xs => exact .cons (removeAfter ys x xs) (permutationBlocks xs ys)
termination_by sizeOf xs

theorem copiesPaper (S : Signature) (f : Head) (τ : Ty) (base extras qs : Args)
    (hp : PaperTerm S (.marked f τ base extras) τ) :
    PaperTerm S (.marked f τ base (copies f base extras qs)) τ := by
  have hc := OwnerRefinementProof.copiesExtras S f τ base extras _ hp (copiesPrefix f base extras qs)
  cases hp.1 with
  | marked hb he => exact ⟨.marked hb hc.1,hp.2.1,hp.2.2.1,hc.2.1⟩
end LogicLineages.PersistentMarking.ExtraCompressionSupport
