module
public import LogicLineages.PermittedControl.TerminalEntryScanTargets

@[expose] public section
namespace LogicLineages.PermittedControl

private def PrefixSpec (test : Nat → Bool) (T r : Nat) : Prop :=
  (r = 0 ↔ ∀ i : Nat, i ≤ T → test i = false) ∧
  ∀ i : Nat, r = i + 1 ↔
    i ≤ T ∧ test i = true ∧ ∀ j : Nat, j < i → test j = false

private theorem prefix_none {test : Nat → Bool} {T r : Nat} (hr : r = 0)
    (h : ∀ i : Nat, i ≤ T → test i = false) : PrefixSpec test T r := by
  refine ⟨⟨fun _ => h, fun _ => hr⟩,?_⟩
  intro i
  constructor
  · intro hi
    omega
  · rintro ⟨hi,hit,_⟩
    have hfalse := h i hi
    rw [hit] at hfalse
    contradiction

private theorem prefix_hit {test : Nat → Bool} {T r i : Nat} (hr : r = i+1)
    (hi : i ≤ T) (hit : test i = true) (hbefore : ∀ j : Nat, j < i → test j = false) :
    PrefixSpec test T r := by
  refine ⟨?_,?_⟩
  · constructor
    · intro h
      omega
    · intro h
      have hfalse := h i hi
      rw [hit] at hfalse
      contradiction
  · intro j
    constructor
    · intro he
      have hji : j = i := by omega
      subst j
      exact ⟨hi,hit,hbefore⟩
    · rintro ⟨_,hj,hjbefore⟩
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · have hfalse := hjbefore i hlt
        rw [hit] at hfalse
        contradiction
      · exact hr
      · have hfalse := hbefore j hgt
        rw [hj] at hfalse
        contradiction

private theorem scan_prefix (f : Nat → Nat) (n mu T : Nat) :
    PrefixSpec (terminalScanTest f n mu) T (boundedTerminalEntryIndex f n mu T) := by
  induction T with
  | zero =>
    cases h : terminalScanTest f n mu 0 with
    | false =>
      apply prefix_none (by simp only [boundedTerminalEntryIndex,h,Bool.false_eq_true,ite_false])
      intro i hi
      have hiz : i = 0 := by omega
      simpa only [hiz] using h
    | true =>
      apply prefix_hit (i := 0) (by simp only [boundedTerminalEntryIndex,h,ite_true]) le_rfl h
      intro j hj
      omega
  | succ T ih =>
    cases hp : boundedTerminalEntryIndex f n mu T with
    | zero =>
      have hall := ih.1.mp hp
      cases ht : terminalScanTest f n mu (T+1) with
      | false =>
        apply prefix_none (by simp only [boundedTerminalEntryIndex,hp,ht,ite_true,Bool.false_eq_true,ite_false])
        intro i hi
        by_cases he : i=T+1
        · simpa only [he] using ht
        · exact hall i (by omega)
      | true =>
        apply prefix_hit (i := T+1) (by simp only [boundedTerminalEntryIndex,hp,ht,ite_true]) le_rfl ht
        intro j hj
        exact hall j (by omega)
    | succ k =>
      have hspec := (ih.2 k).mp hp
      have hretain : boundedTerminalEntryIndex f n mu (T+1) = k+1 := by
        simp only [boundedTerminalEntryIndex,hp,Nat.succ_ne_zero,ite_false]
      exact prefix_hit hretain (hspec.1.trans (Nat.le_succ _)) hspec.2.1 hspec.2.2

theorem boundedTerminalEntryIndexExact : Targets.BoundedTerminalEntryIndexExact := by
  intro f n mu T
  exact scan_prefix f n mu T

end LogicLineages.PermittedControl
