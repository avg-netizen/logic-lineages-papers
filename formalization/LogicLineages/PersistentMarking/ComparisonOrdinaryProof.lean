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
  | there h ih => exact ⟨hr.1, ih hx hr.2⟩

theorem weakOrdinary (S : Signature) (q t : Expr) (h : Weak S q t) : Ordinary t := by
  apply Weak.rec (motive_1 := fun _ t _ => Ordinary t)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ ts _ => OrdinaryArgs ts)
    (motive_4 := fun _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_6 := fun _ _ _ qs _ => OrdinaryArgs qs) (t := h)
  · intro σ x; trivial
  · intro σ s τ t x _ _ _ _ hw ih
    exact substitutionReflects (.cons (.free σ x) .nil) 0 t ih
  · intro f ss g ts _ _ _ _ hm ih
    exact ih
  · intro f ss t _ _ hw ih
    exact ih
  · intro f τ ss es t i q domains r _ _ _ _ _ hw ih
    exact ih
  · intro f σ τ ss es body x _ _ _ _ hw ih
    exact substitutionReflects (.cons (.free σ x) .nil) 0 body ih
  · intro f ss es g ts _ _ _ hw ih
    exact ih
  · intro f ss es g ts _ _ _ _ _ _ ih
    exact ih
  · intros; trivial
  · trivial
  · intro targets y rest x xs hr hw hm ihw ihm
    exact removeOrdinary targets y rest hr ihw ihm
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intro f base extras q qs hw hs ihw ihs
    exact ⟨ihw, ihs⟩

theorem weakTargetsOrdinary : ComparisonTargets.WeakTargetsOrdinary := weakOrdinary

theorem strictTargetsOrdinary : ComparisonTargets.StrictTargetsOrdinary := by
  intro S q t h
  cases h with
  | intro _ _ _ hw => exact weakOrdinary _ _ _ hw
end LogicLineages.PersistentMarking.ComparisonOrdinaryProof
