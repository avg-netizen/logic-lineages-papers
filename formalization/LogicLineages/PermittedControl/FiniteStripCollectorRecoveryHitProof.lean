module
public import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryReadProof
public import LogicLineages.PermittedControl.FiniteStripRecoveryFoldProof
public import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FieldComparison

private def chosenSingle (x : Nat) (μ : Nat → Nat) (r : NamedOperand) : List (Nat × Nat) :=
  if r.2.rank = x then [(r.1,μ r.1)] else []
private def chosenReads (x : Nat) (μ : Nat → Nat) (rs : List NamedOperand) : List (Nat × Nat) :=
  rs.foldr (fun r tail => chosenSingle x μ r ++ tail) []

private theorem same_rank_read (f ρ : Nat → Nat) (x a : Nat) (op : LowerOperand)
    (hx : op.rank = x) (hρ : ρ x = a) :
    lowerOperandRead f (fun _ => a) op = lowerOperandRead f ρ op := by
  cases op <;> simp_all [LowerOperand.rank,lowerOperandRead]

private theorem expected_chosen (f ρ μ : Nat → Nat) (x a : Nat) (r : NamedOperand)
    (hpos : 0 < r.1) (hρ : ρ x = a) (hactual : LowerOperandActual f ρ r.2 (μ r.1)) :
    expectedRead f x a r = some (some (chosenSingle x μ r)) := by
  have hn : r.1 ≠ 0 := Nat.ne_of_gt hpos
  by_cases hx : r.2.rank = x
  · have hh := (preparedTiedProjection.1 f ρ r.2 (μ r.1)).mpr hactual
    have hc : lowerOperandRead f (fun _ => a) r.2 = some (some (μ r.1)) :=
      (same_rank_read f ρ x a r.2 hx hρ).trans hh
    simp [expectedRead,chosenSingle,hn,hx,hc]
  · simp [expectedRead,chosenSingle,hn,hx]

private theorem expected_collect_chosen (f ρ μ : Nat → Nat) (x a : Nat)
    (rs : List NamedOperand) (hpos : ∀ r ∈ rs, 0 < r.1) (hρ : ρ x = a)
    (hactual : ∀ r ∈ rs, LowerOperandActual f ρ r.2 (μ r.1)) :
    expectedCollect f x a rs = some (some (chosenReads x μ rs)) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change appendResult (expectedRead f x a r) (expectedCollect f x a rs) = _
    rw [expected_chosen f ρ μ x a r (hpos r (by simp)) hρ (hactual r (by simp)),
      ih (fun q hq => hpos q (by simp [hq])) (fun q hq => hactual q (by simp [hq]))]
    rfl

private theorem chosen_values (x : Nat) (μ : Nat → Nat) (rs : List NamedOperand) :
    ∀ r ∈ chosenReads x μ rs, r.2 = μ r.1 := by
  induction rs with
  | nil => intro r hr; simp [chosenReads] at hr
  | cons q qs ih =>
    intro r hr
    change r ∈ chosenSingle x μ q ++ chosenReads x μ qs at hr
    rcases List.mem_append.mp hr with hl | ht
    · by_cases hx : q.2.rank = x
      · have he : r = (q.1,μ q.1) := by simpa [chosenSingle,hx] using hl
        subst r
        rfl
      · simp [chosenSingle,hx] at hl
    · exact ih r ht

private theorem chosen_contains (x : Nat) (μ : Nat → Nat) (rs : List NamedOperand)
    (r : NamedOperand) (hr : r ∈ rs) (hx : r.2.rank = x) :
    (r.1,μ r.1) ∈ chosenReads x μ rs := by
  induction rs with
  | nil => simp at hr
  | cons q qs ih =>
    change (r.1,μ r.1) ∈ chosenSingle x μ q ++ chosenReads x μ qs
    rcases List.mem_cons.mp hr with he | ht
    · subst r
      exact List.mem_append_left _ (by simp [chosenSingle,hx])
    · exact List.mem_append_right _ (ih ht)

private theorem valuation_correct (reads : List (Nat × Nat)) (ν μ : Nat → Nat) (i : Nat)
    (hv : ∀ r ∈ reads, r.2 = μ r.1)
    (hi : ν i = μ i ∨ i ∈ reads.map Prod.fst) :
    FiniteStripRecovery.foldValuation reads ν i = μ i := by
  induction reads generalizing ν with
  | nil =>
    rcases hi with h | h
    · exact h
    · simp at h
  | cons r rs ih =>
    have ht : ∀ q ∈ rs, q.2 = μ q.1 := fun q hq => hv q (by simp [hq])
    apply ih (Function.update ν r.1 r.2) ht
    by_cases he : i = r.1
    · left
      subst i
      simpa using hv r (by simp)
    · rcases hi with hh | hh
      · left
        simpa [Function.update_of_ne he] using hh
      · right
        have hm : i = r.1 ∨ i ∈ rs.map Prod.fst := List.mem_cons.mp hh
        exact hm.resolve_left he

theorem collectorHitFold : CollectorHitFold := by
  intro f x a rs reads p ρ ν μ hpos _hnodup hsupport hhit hρ hactual hagree
  have he : reads = chosenReads x μ rs := by
    have hh := (collect_code f x a rs).trans
      (expected_collect_chosen f ρ μ x a rs hpos hρ hactual)
    rw [hhit] at hh
    exact Option.some.inj (Option.some.inj hh)
  subst reads
  apply FiniteStripRecovery.foldDualValuation
  intro i hi
  apply valuation_correct _ ν μ i (chosen_values x μ rs)
  obtain ⟨r,hr,he⟩ := List.mem_map.mp (hsupport i hi)
  by_cases hx : r.2.rank = x
  · right
    exact List.mem_map.mpr ⟨(r.1,μ r.1),chosen_contains x μ rs r hr hx,he⟩
  · left
    simpa only [he] using hagree r hr hx
end LogicLineages.PermittedControl.FiniteStripCollectorRecovery
