module
public import LogicLineages.PersistentMarking.NumberedWindowCoverGrammarMonotoneTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverGrammarMonotone
open NumberedWindowCoverAlgorithm

private theorem mapSub {α β : Type} (f : α → β) {xs ys : List α}
    (h : xs ⊆ ys) : xs.map f ⊆ ys.map f := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨a,ha,rfl⟩
  exact List.mem_map.mpr ⟨a,h ha,rfl⟩

private theorem flatSub {α β : Type} {f g : α → List β} {xs ys : List α}
    (h : xs ⊆ ys) (hi : ∀ a, f a ⊆ g a) : xs.flatMap f ⊆ ys.flatMap g := by
  intro b hb
  rcases List.mem_flatMap.mp hb with ⟨a,ha,hb⟩
  exact List.mem_flatMap.mpr ⟨a,h ha,hi a hb⟩

private theorem appendSub {α : Type} {xs ys ws zs : List α}
    (ha : xs ⊆ ys) (hb : ws ⊆ zs) : xs ++ ws ⊆ ys ++ zs := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact List.mem_append.mpr (.inl (ha h))
  · exact List.mem_append.mpr (.inr (hb h))

private theorem reflSub {α : Type} (xs : List α) : xs ⊆ xs := fun h => h

private theorem leavesSub (K : List Nat) {I J : List Nat} (ij : I ⊆ J) :
    leaves K I ⊆ leaves K J := by
  unfold leaves namedLeaves
  exact appendSub
    (appendSub (flatSub (reflSub K) (fun _ => mapSub _ ij))
      (flatSub (reflSub K) (fun _ => mapSub _ ij)))
    (reflSub _)

private theorem termsStepSub (H K : List Nat) {I J ts us xs ys : List Nat}
    (ij : I ⊆ J) (tu : ts ⊆ us) (xy : xs ⊆ ys) :
    leaves K I ++ lambdas K ts ++ ordinary H xs ++ numbered H K I xs ++ applications K ts ⊆
    leaves K J ++ lambdas K us ++ ordinary H ys ++ numbered H K J ys ++ applications K us := by
  have hλ : lambdas K ts ⊆ lambdas K us := flatSub (reflSub K) (fun _ => mapSub _ tu)
  have ho : ordinary H xs ⊆ ordinary H ys := flatSub (reflSub H) (fun _ => mapSub _ xy)
  have hn : numbered H K I xs ⊆ numbered H K J ys :=
    flatSub (reflSub H) (fun _ => flatSub (reflSub K) (fun _ => flatSub ij
      (fun _ => flatSub xy (fun _ => mapSub _ xy))))
  have happ : applications K ts ⊆ applications K us :=
    flatSub (reflSub K) (fun _ => flatSub (reflSub K) (fun _ => flatSub tu (fun _ => mapSub _ tu)))
  exact appendSub (appendSub (appendSub (appendSub (leavesSub K ij) hλ) ho) hn) happ

private theorem argsStepSub {ts us xs ys : List Nat} (tu : ts ⊆ us) (xy : xs ⊆ ys) :
    cells ts xs ⊆ cells us ys := by
  unfold cells
  intro n h
  rcases List.mem_cons.mp h with h | h
  · exact List.mem_cons.mpr (.inl h)
  · exact List.mem_cons.mpr (.inr (flatSub tu (fun _ => mapSub _ xy) h))

private theorem rangeSub {m n : Nat} (h : m ≤ n) : List.range m ⊆ List.range n := by
  intro a ha
  exact List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp ha) h)

private theorem stepSub (H K : List Nat) {m n d e : Nat} (hm : m ≤ n)
    (ht : (grammar H K m d).1 ⊆ (grammar H K n e).1)
    (hx : (grammar H K m d).2 ⊆ (grammar H K n e).2) :
    (grammar H K m (d+1)).1 ⊆ (grammar H K n (e+1)).1 ∧
    (grammar H K m (d+1)).2 ⊆ (grammar H K n (e+1)).2 := by
  simp only [grammar]
  exact ⟨termsStepSub H K (rangeSub (Nat.succ_le_succ hm)) ht hx, argsStepSub ht hx⟩

private theorem numeralSub (H K : List Nat) {m n : Nat} (h : m ≤ n) (d : Nat) :
    (grammar H K m d).1 ⊆ (grammar H K n d).1 ∧
    (grammar H K m d).2 ⊆ (grammar H K n d).2 := by
  induction d with
  | zero => exact ⟨reflSub _,reflSub _⟩
  | succ d ih => exact stepSub H K h ih.1 ih.2

private theorem nextDepthSub (H K : List Nat) (m d : Nat) :
    (grammar H K m d).1 ⊆ (grammar H K m (d+1)).1 ∧
    (grammar H K m d).2 ⊆ (grammar H K m (d+1)).2 := by
  induction d with
  | zero =>
      constructor
      · intro n h
        exact (List.not_mem_nil h).elim
      · intro n h
        have hn : n = 0 := by simpa [grammar] using h
        subst n
        simp [grammar,cells]
  | succ d ih => exact stepSub H K (Nat.le_refl m) ih.1 ih.2

private theorem depthSub (H K : List Nat) (m : Nat) {d e : Nat} (h : d ≤ e) :
    (grammar H K m d).1 ⊆ (grammar H K m e).1 ∧
    (grammar H K m d).2 ⊆ (grammar H K m e).2 := by
  induction h with
  | refl => exact ⟨reflSub _,reflSub _⟩
  | @step e _ ih =>
      have step := nextDepthSub H K m e
      exact ⟨fun h => step.1 (ih.1 h),fun h => step.2 (ih.2 h)⟩

theorem boundsInclusion : ExactGrammarBoundsInclusion := by
  intro H K m n d e hm hd
  have h1 := numeralSub H K hm d
  have h2 := depthSub H K n hd
  exact ⟨fun h => h2.1 (h1.1 h),fun h => h2.2 (h1.2 h)⟩

end LogicLineages.PersistentMarking.NumberedWindowCoverGrammarMonotone
