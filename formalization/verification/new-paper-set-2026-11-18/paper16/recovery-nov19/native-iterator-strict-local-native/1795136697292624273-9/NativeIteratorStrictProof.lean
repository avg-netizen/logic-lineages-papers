import LogicLineages.PersistentMarking.NativeIteratorStrictTargets
import LogicLineages.PersistentMarking.NativeIteratorChecks
import LogicLineages.PersistentMarking.NativeOrientationChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalWellFoundedChecks
import LogicLineages.PersistentMarking.DecisionSourceConstructProof
import LogicLineages.PersistentMarking.FreeVariableProof

namespace LogicLineages.PersistentMarking.NativeIteratorStrictProof
open Spine NameBridge NativeReduction NativeCarrierTargets NativeIndexedCarrierTargets
open NativeIteratorTargets NativeIteratorStrictTargets
open DecisionInventory (heads headsArgs)

mutual
private theorem absentHead (f : Head) (a : Expr) (ha : f ∉ heads a) (d : Nat) (q : Expr)
    (h : f ∉ heads q) : f ∉ heads (substitute (.cons a .nil) d q) := by
  cases q with
  | free σ i => exact h
  | bound σ i =>
    by_cases hBelow : i < d
    · simp [substitute, hBelow, heads]
    · cases hIndex : i - d with
      | zero =>
        simp only [substitute, hBelow, if_false, hIndex, Args.get]
        rw [(DecisionSourceConstructProof.shiftFacts d 0 a).2.1]
        exact ha
      | succ j => simp [substitute, hBelow, hIndex, Args.get, heads]
  | lam σ body => exact absentHead f a ha (d + 1) body h
  | head g base =>
    intro hf
    rcases List.mem_cons.mp hf with hSame | hMore
    · exact h (List.mem_cons.mpr (Or.inl hSame))
    · exact absentArgsHead f a ha d base (fun hx => h (List.mem_cons_of_mem _ hx)) hMore
  | marked g τ base extra =>
    intro hf
    rcases List.mem_cons.mp hf with hSame | hMore
    · exact h (List.mem_cons.mpr (Or.inl hSame))
    · rcases List.mem_append.mp hMore with hb | he
      · exact absentArgsHead f a ha d base
          (fun hx => h (List.mem_cons_of_mem _ (List.mem_append_left _ hx))) hb
      · exact absentArgsHead f a ha d extra
          (fun hx => h (List.mem_cons_of_mem _ (List.mem_append_right _ hx))) he
termination_by sizeOf q

private theorem absentArgsHead (f : Head) (a : Expr) (ha : f ∉ heads a) (d : Nat) (qs : Args)
    (h : f ∉ headsArgs qs) : f ∉ headsArgs (substituteArgs (.cons a .nil) d qs) := by
  cases qs with
  | nil => exact h
  | cons q tail =>
    intro hf
    rcases List.mem_append.mp hf with hq | hTail
    · exact absentHead f a ha d q (fun hx => h (List.mem_append_left _ hx)) hq
    · exact absentArgsHead f a ha d tail (fun hx => h (List.mem_append_right _ hx)) hTail
termination_by sizeOf qs
end

private theorem nativeSubstitute {q a : Expr} (hq : Native q) (ha : Native a) :
    Native (substitute (.cons a .nil) 0 q) :=
  fun name arity => absentHead (.ranked name arity) a (ha name arity) 0 q (hq name arity)

private theorem nativeApp {σ τ q a} (hq : Native q) (ha : Native a) : Native (app σ τ q a) := by
  intro name arity
  simp [app, heads, headsArgs, hq name arity, ha name arity]

private theorem strictTargetClosed {S τ s t} (hs : ClosedNative S s τ) (h : ConfinedPair.Strict S s t) :
    ClosedOrdinary S t τ := by
  obtain ⟨⟨ρ, hSource, hTarget, _, hOrdinary⟩, hStrict, _⟩ := h
  have hType : ρ = τ := (SpineShiftProof.annotationExact _ _ _ hSource.1).symm.trans
    (SpineShiftProof.annotationExact _ _ _ hs.1.1.1)
  subst ρ
  refine ⟨hTarget, hOrdinary, ?_⟩
  intro name
  cases hFree : freeOccurs name t with
  | false => rfl
  | true =>
    have hf := FreeVariableProof.strictContainment S s t hStrict name hFree
    rw [hs.1.2.2 name] at hf
    cases hf

theorem wf : ClosedNativeStrictWellFounded := by
  intro S τ
  exact InvImage.wf Subtype.val (NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded S)

theorem chain : IteratorNativeStrictChain := by
  intro S A i p u hi hp hu
  let B := actualType A
  let η := functionType A
  have hIterator := NativeIteratorChecks.exact_ClosedNativeIterator S A
  have hStart : ClosedNative S (applied A i p u) B :=
    NativeClosedProof.application S B B _ u
      (NativeClosedProof.application S η η _ p
        (NativeClosedProof.application S indexType (.arrow η η) _ i hIterator hi) hp) hu
  obtain ⟨edgeI, edgeP, edgeU⟩ := NativeIteratorChecks.exact_IteratorNativeBetaTransport S A i p u hi hp hu
  have strictI := NativeOrientationChecks.exact_fullOrientation S _ _ edgeI
  have strictP := NativeOrientationChecks.exact_fullOrientation S _ _ edgeP
  have strictU := NativeOrientationChecks.exact_fullOrientation S _ _ edgeU

  have hPartI : Native (.lam η (.lam B (afterIndexBody A i))) :=
    nativeSubstitute (q := .lam η (.lam B (iteratorBody A))) hIterator.2 hi.2
  have hNativeI : Native (afterIndex A i p u) := nativeApp (nativeApp hPartI hp.2) hu.2
  have hIndex : ClosedNative S (afterIndex A i p u) B := ⟨strictTargetClosed hStart strictI, hNativeI⟩

  have hPartP : Native (.lam B (afterFunctionBody A i p)) :=
    nativeSubstitute (q := .lam B (afterIndexBody A i)) hPartI hp.2
  have hFunction : ClosedNative S (afterFunction A i p u) B :=
    ⟨strictTargetClosed hIndex strictP, nativeApp hPartP hu.2⟩
  have hFinal := NativeIndexedTypingThinProof.indexedClosed S A p u i hp hu hi
  exact ⟨⟨_, hStart⟩, ⟨_, hIndex⟩, ⟨_, hFunction⟩, ⟨_, hFinal⟩,
    rfl, rfl, rfl, rfl, strictI, strictP, strictU⟩

end LogicLineages.PersistentMarking.NativeIteratorStrictProof
