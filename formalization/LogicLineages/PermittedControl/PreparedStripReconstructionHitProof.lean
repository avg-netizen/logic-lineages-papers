module
public import LogicLineages.PermittedControl.PreparedStripReconstructionTargets
import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryReadProof
import LogicLineages.PermittedControl.FiniteStripRecoveryFoldProof
import LogicLineages.PermittedControl.PreparedParameterActualProof
import Mathlib.Data.List.Nodup

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedStripReconstruction
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FiniteStripRecovery FiniteStripCollectorRecovery

private theorem append_hit (u v : ReadResult) (reads : List (Nat × Nat))
    (h : appendResult u v = some (some reads)) :
    ∃ hs ts : List (Nat × Nat), u = some (some hs) ∧ v = some (some ts) ∧ reads = hs ++ ts := by
  cases u with
  | none => simp [appendResult] at h
  | some u =>
    cases u with
    | none => simp [appendResult] at h
    | some hs =>
      cases v with
      | none => simp [appendResult] at h
      | some v =>
        cases v with
        | none => simp [appendResult] at h
        | some ts =>
          have he : hs ++ ts = reads := by simpa [appendResult] using h
          exact ⟨hs,ts,rfl,rfl,he.symm⟩

private theorem single_hit (f : Nat → Nat) (x a : Nat) (r : NamedOperand)
    (hs : List (Nat × Nat)) (hh : expectedRead f x a r = some (some hs)) :
    ((r.2.rank ≠ x) ∧ hs = []) ∨
    ∃ v : Nat, r.2.rank = x ∧ lowerOperandRead f (fun _ => a) r.2 = some (some v) ∧
      hs = [(r.1,v)] := by
  by_cases hn : r.1 = 0
  · simp [expectedRead,hn] at hh
  by_cases hx : r.2.rank = x
  · cases hread : lowerOperandRead f (fun _ => a) r.2 with
    | none => simp [expectedRead,hn,hx,hread] at hh
    | some u =>
      cases u with
      | none => simp [expectedRead,hn,hx,hread] at hh
      | some v =>
        have he : [(r.1,v)] = hs := by simpa [expectedRead,hn,hx,hread] using hh
        exact Or.inr ⟨v,hx,rfl,he.symm⟩
  · have he : [] = hs := by simpa [expectedRead,hn,hx] using hh
    exact Or.inl ⟨hx,he.symm⟩

/-- The successful list uses only actual matching reads, and no original
matching request is omitted. Both properties follow from the ordered fold. -/
private theorem expected_hit (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand)
    (reads : List (Nat × Nat)) (h : expectedCollect f x a rs = some (some reads)) :
    (∀ z ∈ reads, ∃ r ∈ rs, r.1 = z.1 ∧ r.2.rank = x ∧
      lowerOperandRead f (fun _ => a) r.2 = some (some z.2)) ∧
    ∀ r ∈ rs, r.2.rank = x → ∃ v : Nat, (r.1,v) ∈ reads ∧
      lowerOperandRead f (fun _ => a) r.2 = some (some v) := by
  induction rs generalizing reads with
  | nil =>
    have he : [] = reads := by simpa [expectedCollect] using h
    subst reads
    simp
  | cons r rs ih =>
    change appendResult (expectedRead f x a r) (expectedCollect f x a rs) =
      some (some reads) at h
    obtain ⟨hs,ts,hh,ht,rfl⟩ := append_hit _ _ _ h
    obtain ⟨hsound,hcover⟩ := ih ts ht
    have htail : ∀ z ∈ ts, ∃ q ∈ r :: rs, q.1 = z.1 ∧ q.2.rank = x ∧
        lowerOperandRead f (fun _ => a) q.2 = some (some z.2) := by
      intro z hz
      obtain ⟨q,hq,hn,hx,hread⟩ := hsound z hz
      exact ⟨q,List.mem_cons_of_mem _ hq,hn,hx,hread⟩
    rcases single_hit f x a r hs hh with ⟨hneq,rfl⟩ | ⟨v,hx,hread,rfl⟩
    · refine ⟨by simpa using htail,?_⟩
      intro q hq hqx
      rcases List.mem_cons.mp hq with he | htq
      · subst q
        exact (hneq hqx).elim
      · simpa using hcover q htq hqx
    · constructor
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · have he : z = (r.1,v) := List.mem_singleton.mp hz
          subst z
          exact ⟨r,by simp,rfl,hx,hread⟩
        · exact htail z hz
      · intro q hq hqx
        rcases List.mem_cons.mp hq with he | htq
        · subst q
          exact ⟨v,by simp,hread⟩
        · obtain ⟨w,hw,hqread⟩ := hcover q htq hqx
          exact ⟨w,List.mem_append_right _ hw,hqread⟩

private theorem fold_at (reads : List (Nat × Nat)) (ν : Nat → Nat) (i v : Nat)
    (hv : ∀ w : Nat, (i,w) ∈ reads → w = v)
    (h : ν i = v ∨ ∃ w : Nat, (i,w) ∈ reads) :
    foldValuation reads ν i = v := by
  induction reads generalizing ν with
  | nil =>
    rcases h with he | ⟨w,hw⟩
    · exact he
    · simp at hw
  | cons r rs ih =>
    change foldValuation rs (Function.update ν r.1 r.2) i = v
    apply ih _ (fun w hw => hv w (List.mem_cons_of_mem _ hw))
    by_cases he : i = r.1
    · left
      have hr : (i,r.2) = r := Prod.ext he rfl
      have hrv : r.2 = v := hv r.2 (by rw [hr]; simp)
      simpa only [he,Function.update_self] using hrv
    · rw [Function.update_of_ne he]
      rcases h with h0 | ⟨w,hw⟩
      · exact Or.inl h0
      · rcases List.mem_cons.mp hw with hr | ht
        · exact (he (congrArg Prod.fst hr)).elim
        · exact Or.inr ⟨w,ht⟩

private theorem same_rank_read (f ρ : Nat → Nat) (x a : Nat) (op : LowerOperand)
    (hx : op.rank = x) (hρ : ρ x = a) :
    lowerOperandRead f (fun _ => a) op = lowerOperandRead f ρ op := by
  cases op <;> simp_all [LowerOperand.rank,lowerOperandRead]

theorem hitReconstruction : HitReconstruction := by
  intro f x a rs p reads ρ ν hin hhit hρ hrest
  obtain ⟨hplain,_,huniq,hsupport⟩ := hin
  have he : expectedCollect f x a rs = some (some reads) :=
    (collect_code f x a rs).symm.trans hhit
  obtain ⟨hsound,hcover⟩ := expected_hit f x a rs reads he
  refine ⟨?_,foldActual reads p ν,foldPlain reads p hplain,?_⟩
  · intro r hr
    by_cases hx : r.2.rank = x
    · obtain ⟨v,hv,hread⟩ := hcover r hr hx
      have hup : foldValuation reads ν r.1 = v := by
        apply fold_at reads ν r.1 v _ (Or.inr ⟨v,hv⟩)
        intro w hw
        obtain ⟨q,hq,hn,_,hqread⟩ := hsound (r.1,w) hw
        have hqr : q = r := List.inj_on_of_nodup_map huniq hq hr hn
        subst q
        exact Option.some.inj (Option.some.inj (hqread.symm.trans hread))
      change LowerOperandActual f ρ r.2 (foldValuation reads ν r.1)
      rw [hup]
      exact (preparedTiedProjection.1 f ρ r.2 v).mp
        ((same_rank_read f ρ x a r.2 hx hρ).symm.trans hread)
    · have hup : foldValuation reads ν r.1 = ν r.1 := by
        apply fold_at reads ν r.1 (ν r.1) _ (Or.inl rfl)
        intro w hw
        obtain ⟨q,hq,hn,hqx,_⟩ := hsound (r.1,w) hw
        have hqr : q = r := List.inj_on_of_nodup_map huniq hq hr hn
        subst q
        exact (hx hqx).elim
      change LowerOperandActual f ρ r.2 (foldValuation reads ν r.1)
      rw [hup]
      exact hrest r hr hx
  · intro i hi
    obtain ⟨ha,ho⟩ := (foldSupport reads p i).mp hi
    obtain ⟨r,hr,hn⟩ := List.mem_map.mp (hsupport i ho)
    refine ⟨r,hr,hn,?_⟩
    intro hx
    obtain ⟨v,hv,_⟩ := hcover r hr hx
    exact ha (List.mem_map.mpr ⟨(r.1,v),hv,hn⟩)

end LogicLineages.PermittedControl.PreparedStripReconstruction
