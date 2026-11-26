import LogicLineages.PersistentMarking.UnaryTransportSupport
import LogicLineages.PersistentMarking.ExtraCompressionSupport
namespace LogicLineages.PersistentMarking.UnaryPermutationSupport
open Spine

theorem removeAppend {xs ys : Args} {q : Expr} (h : Remove xs q ys) (tail : Args) :
    Remove (xs.append tail) q (ys.append tail) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem permutationAppend {xs ys : Args} (h : Permutation xs ys) (tail : Args) :
    Permutation (xs.append tail) (ys.append tail) := by
  induction h with
  | nil => exact ExtraCompressionSupport.permutationRefl tail
  | cons hr _ ih => exact .cons (removeAppend hr tail) ih

theorem permutationPrefix (front : Args) {xs ys : Args} (h : Permutation xs ys) :
    Permutation (front.append xs) (front.append ys) := by
  cases front with
  | nil => exact h
  | cons x front => exact .cons .here (permutationPrefix front h)
termination_by sizeOf front

theorem swapSuffix (front xs ys : Args) :
    Permutation ((front.append xs).append ys) ((front.append ys).append xs) := by
  simpa only [PrefixStageSupport.appendAssoc] using permutationPrefix front (ExtraCompressionSupport.permutationBlocks xs ys)

theorem prefixExtend {xs ys : Args} (h : Prefix xs ys) (tail : Args) : Prefix xs (ys.append tail) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem copyExtend {f : Head} {base extras : Args} {σ : Ty} {q : Expr}
    (h : PrefixCopy f base extras σ q) (tail : Args) : PrefixCopy f base (extras.append tail) σ q := by
  cases h with
  | intro hp => exact .intro (prefixExtend hp tail)

theorem copiesExtend {f : Head} {base extras xs : Args}
    (h : PrefixCopies f base extras xs) (tail : Args) : PrefixCopies f base (extras.append tail) xs := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (copyExtend hc tail) ih

theorem tupleExtend {f : Head} {base extras xs : Args} {types : List Ty}
    (h : PrefixTuple f base extras types xs) (tail : Args) : PrefixTuple f base (extras.append tail) types xs := by
  induction h with
  | nil => exact .nil
  | cons hc _ ih => exact .cons (copyExtend hc tail) ih

theorem tupleAppend {f : Head} {base extras xs ys : Args} {types more : List Ty}
    (h : PrefixTuple f base extras types xs) (hy : PrefixTuple f base extras more ys) :
    PrefixTuple f base extras (types ++ more) (xs.append ys) := by
  induction h with
  | nil => exact hy
  | cons hc _ ih => exact .cons hc ih

theorem arrowAppend (types more : List Ty) (τ : Ty) : ArrowPrefix (types ++ more) τ = ArrowPrefix types (ArrowPrefix more τ) := by
  induction types with
  | nil => rfl
  | cons σ types ih => simp only [List.cons_append,ArrowPrefix,ih]
end LogicLineages.PersistentMarking.UnaryPermutationSupport
