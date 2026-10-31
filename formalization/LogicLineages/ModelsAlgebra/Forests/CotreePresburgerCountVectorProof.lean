module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVectorTargets
public import Mathlib.Data.List.OfFn
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.Proof
open CotreePresburger CotreePresburgerPullback

theorem count_chunks {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → List β) (b : β) :
    (xs.flatMap f).count b = (xs.map (fun a => (f a).count b)).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem sum_elements {α : Type} [Fintype α] [LinearOrder α] (f : α → Nat) :
    ((elements α).map f).sum = ∑ a, f a := by
  rw [elements, ← List.sum_toFinset _ (Finset.sort_nodup _ _)]
  simp

theorem countsExact : Targets.CountsExact := by
  intro Q _ _ v
  funext q
  rw [CotreePresburgerPullback.StatementChecks.wordCountsEqCount,
    realizeCounts, count_chunks, sum_elements]
  simp [List.count_replicate, beq_iff_eq]

theorem count_realizeCounts {Q : Type} [Fintype Q] [LinearOrder Q] (v : Q → Nat) (q : Q) :
    (realizeCounts v).count q = v q := by
  rw [← CotreePresburgerPullback.StatementChecks.wordCountsEqCount]
  exact congrFun (countsExact Q v) q

theorem lengthExact : Targets.LengthExact := by
  intro Q _ _ v
  calc
    _ = ∑ q, (realizeCounts v).count q :=
      (CotreePresburgerProjection.StatementChecks.wordTotalCounts Q (realizeCounts v)).symm
    _ = ∑ q, v q := Finset.sum_congr rfl (fun q _ => count_realizeCounts v q)

theorem membershipExact : Targets.MembershipExact := by
  intro Q _ _ v q
  rw [← List.count_pos_iff, count_realizeCounts]

theorem childrenExact : Targets.ChildrenExact := by
  intro Q _ _ v hv
  let w := realizeCounts v
  have hw : 2 ≤ w.length := by simpa only [w, lengthExact Q v] using hv
  let n := w.length - 2
  have hn : n + 2 = w.length := by omega
  refine ⟨n, fun i => w.get (Fin.cast hn i), ?_⟩
  exact (List.ofFn_congr hn.symm w.get).symm.trans (List.ofFn_get w)

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCountVector.Proof
