import LogicLineages.PersistentMarking.PrefixSplicingProof
namespace LogicLineages.PersistentMarking.PrefixStageSupport
open Spine

theorem appendNil (xs : Args) : xs.append .nil = xs := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [Args.append,appendNil xs]
termination_by sizeOf xs

theorem appendAssoc (xs ys zs : Args) : (xs.append ys).append zs = xs.append (ys.append zs) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [Args.append,appendAssoc xs ys zs]
termination_by sizeOf xs

theorem consumeAppend (σ : Ty) (xs ys : Args) :
    consumeTypes σ (xs.append ys) = (consumeTypes σ xs).bind (fun ρ => consumeTypes ρ ys) := by
  cases xs with
  | nil => simp only [Args.append,consumeTypes,Option.bind_some]
  | cons x xs =>
    cases σ with
    | ground => rfl
    | arrow α β =>
      by_cases ht : x.type = α
      · simpa only [Args.append,consumeTypes,ht,if_true] using consumeAppend β xs ys
      · simp [Args.append,consumeTypes,ht]
termination_by sizeOf xs

theorem markedAfter (g : Head) (σ ρ : Ty) (base extras first second : Args) (w : Expr)
    (hfirst : consumeTypes σ first = some ρ)
    (hsecond : apply (.marked g ρ base (extras.append first)) second = some w) :
    ∃ τ, consumeTypes σ (first.append second) = some τ ∧
      w = .marked g τ base (extras.append (first.append second)) := by
  cases second with
  | nil =>
    simp only [apply,Option.some.injEq] at hsecond
    exact ⟨ρ,by simpa only [appendNil] using hfirst,by simpa only [appendNil] using hsecond.symm⟩
  | cons b bs =>
    cases ht : consumeTypes ρ (.cons b bs) with
    | none => simp [apply,applyAux,ht] at hsecond
    | some τ =>
      simp only [apply,applyAux,ht,Option.map_some,SubstitutionProof.emptyArgsSubstitution,Option.some.injEq] at hsecond
      refine ⟨τ,?_,?_⟩
      · simp only [consumeAppend,hfirst,Option.bind_some,ht]
      · simpa only [appendAssoc] using hsecond.symm
end LogicLineages.PersistentMarking.PrefixStageSupport
