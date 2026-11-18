import LogicLineages.PersistentMarking.RankedRestrictionSplitProof

namespace LogicLineages.PersistentMarking.RankedRestrictionCoverageProof
open Spine RankedRestrictionTargets

theorem move (S : Signature) {xs ys ts : Args}
    (h : RPOCoverage S xs ts) (hm : ∀ i q, At xs i q → ∃ j, At ys j q) :
    RPOCoverage S ys ts := by
  cases ts with
  | nil => exact .nil
  | cons t ts =>
    cases h with
    | cons hAt hWeak hRest =>
      obtain ⟨j,hj⟩ := hm _ _ hAt
      exact .cons hj hWeak (move S (xs := xs) (ys := ys) (ts := ts) hRest hm)
termination_by sizeOf ts

theorem insert (S : Signature) {xs ts rest : Args} {q t : Expr} {i : Nat}
    (hc : RPOCoverage S xs rest) (h : Remove ts t rest) (hq : At xs i q) (hr : RPO S q t) :
    RPOCoverage S xs ts := by
  induction h with
  | here => exact .cons hq hr hc
  | there _ ih =>
    cases hc with
    | cons ha hb hc => exact .cons ha hb (ih hc hr)

theorem merge (S : Signature) (xs : Args) {ts ts₁ ts₂ : Args} (h : Split ts ts₁ ts₂)
    (h₁ : RPOCoverage S xs ts₁) (h₂ : RPOCoverage S xs ts₂) : RPOCoverage S xs ts := by
  induction h with
  | nil => exact .nil
  | left _ ih =>
    cases h₁ with
    | cons ha hr ht => exact .cons ha hr (ih ht h₂)
  | right _ ih =>
    cases h₂ with
    | cons ha hr ht => exact .cons ha hr (ih h₁ ht)

theorem emptyOwners (S : Signature) (ts : Args) (h : RPOCoverage S .nil ts) : ts = .nil := by
  cases h with
  | nil => rfl
  | cons ha => cases ha

end LogicLineages.PersistentMarking.RankedRestrictionCoverageProof
