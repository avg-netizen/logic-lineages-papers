import LogicLineages.PersistentMarking.ComparisonTargets
namespace LogicLineages.PersistentMarking.ComparisonOrdinaryProof
open Spine

mutual
 theorem substitutionReflects (values : Args) (depth : Nat) (q : Expr)
    (h : Ordinary (substitute values depth q)) : Ordinary q := by
  cases q with
  | free σ x => trivial
  | bound σ i => trivial
  | lam σ body => exact substitutionReflects values (depth+1) body h
  | head f base => exact substitutionArgsReflects values depth base h
  | marked f τ base extras => exact h
 termination_by sizeOf q
 theorem substitutionArgsReflects (values : Args) (depth : Nat) (qs : Args)
    (h : OrdinaryArgs (substituteArgs values depth qs)) : OrdinaryArgs qs := by
  cases qs with
  | nil => trivial
  | cons q qs => exact ⟨substitutionReflects values depth q h.1,
      substitutionArgsReflects values depth qs h.2⟩
 termination_by sizeOf qs
end

theorem removeOrdinary (xs : Args) (x : Expr) (rest : Args) (h : Remove xs x rest)
    (hx : Ordinary x) (hr : OrdinaryArgs rest) : OrdinaryArgs xs := by
  induction h with
  | here => exact ⟨hx,hr⟩
  | there h ih => exact ⟨hr.1, ih hr.2⟩

mutual
 theorem weakOrdinary (S : Signature) (q t : Expr) (h : Weak S q t) : Ordinary t := by
  cases h with
  | var => trivial
  | abs _ _ _ _ hw =>
    exact substitutionReflects _ _ _ (weakOrdinary _ _ _ hw)
  | funHead _ _ _ _ hm => exact matchingOrdinary _ _ _ hm
  | put _ _ hw => exact weakOrdinary _ _ _ hw
  | select _ _ _ _ _ hw => exact weakOrdinary _ _ _ hw
  | fabs _ _ _ _ hw =>
    exact substitutionReflects _ _ _ (weakOrdinary _ _ _ hw)
  | copy _ _ _ hw => exact wholeOrdinary _ _ _ _ _ hw
  | stat _ _ _ _ hw => exact wholeOrdinary _ _ _ _ _ hw
 termination_by structural h
 theorem matchingOrdinary (S : Signature) (xs ys : Args) (h : Matching S xs ys) : OrdinaryArgs ys := by
  cases h with
  | nil => trivial
  | cons hr hw hm => exact removeOrdinary _ _ _ hr (weakOrdinary _ _ _ hw) (matchingOrdinary _ _ _ hm)
 termination_by structural h
 theorem wholeOrdinary (S : Signature) (f : Head) (base extras qs : Args)
    (h : Whole S f base extras qs) : OrdinaryArgs qs := by
  cases h with
  | nil => trivial
  | cons hw hs => exact ⟨weakOrdinary _ _ _ hw, wholeOrdinary _ _ _ _ _ hs⟩
 termination_by structural h
end

theorem weakTargetsOrdinary : ComparisonTargets.WeakTargetsOrdinary := weakOrdinary

theorem strictTargetsOrdinary : ComparisonTargets.StrictTargetsOrdinary := by
  intro S q t h
  cases h with
  | intro _ _ _ hw => exact weakOrdinary _ _ _ hw
end LogicLineages.PersistentMarking.ComparisonOrdinaryProof
