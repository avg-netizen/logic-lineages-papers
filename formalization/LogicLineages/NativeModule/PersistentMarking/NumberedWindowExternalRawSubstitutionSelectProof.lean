module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalRawSubstitutionTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationHeadProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionSelectProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowExternalRawSubstitutionTargets NumberedWindowPreservationGuardProof
open Spine (ArrowPrefix)
open NumberedWindowApplicationTargets (ArgsWindow)
open NumberedWindowApplicationDomainProof (app appEq annotation rootInWindow arrowLeft arrowRight subtypeSelf)
open NumberedWindowNumberedDomainProof (ArgsGuard parts)
open NumberedWindowPreservationSubstitutionProof (term)

theorem applicationsCommute : TypedSubstitutionApplications := by
  intro S K C D ds τ q args values d hk hc hq hArgs
  induction hArgs generalizing q with
  | nil => rfl
  | cons ha _ ih =>
    have hf := term S K hk values d C D _ _ hq hc
    have hu := term S K hk values d C D _ _ ha hc
    rw [substituteArgs, appEq hf.1 hu.1, appEq hq.1 ha.1]
    exact ih _ (app S K C _ _ _ _ hk hq ha)

private theorem sourceAt {S K C xs q} (ht : ExtrasTyped C xs) (hg : ArgsGuard S K xs)
    (i : Nat) (h : xs.get i = some q) : InWindow S K C q.type q := by
  cases ht with
  | nil => cases h
  | cons ha hTail =>
    obtain ⟨hGuard, hGuards⟩ := consParts hg
    cases i with
    | zero =>
      have e := Option.some.inj h
      subst q
      exact ⟨(annotation ha).symm ▸ ha, hGuard⟩
    | succ i => exact sourceAt hTail hGuards i h
termination_by i

private theorem mappedGet (values xs : NArgs) (d i : Nat) :
    (substituteArgs values d xs).get i = (xs.get i).map (substitute values d) := by
  cases xs with
  | nil => rfl
  | cons a rest =>
    cases i with
    | zero => rfl
    | succ i => exact mappedGet values rest d i
termination_by i

theorem mappedCopies (values : NArgs) (d : Nat) (f : Head) (k : Nat)
    (bs es : NArgs) (ds : List Ty) :
    substituteArgs values d (ownerCopies f k bs es ds) =
      ownerCopies f k (substituteArgs values d bs) (substituteArgs values d es) ds := by
  induction ds with
  | nil => rfl
  | cons _ _ ih => simp only [ownerCopies, substituteArgs, substitute, ih]

private theorem arrowDomains {K : List Ty} (hk : DecisionSourceUniverse.Closed K)
    (ds : List Ty) (τ : Ty) (h : ArrowPrefix ds τ ∈ K) : ∀ t ∈ ds, t ∈ K := by
  induction ds with
  | nil => intro t ht; exact (List.not_mem_nil ht).elim
  | cons σ ds ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact arrowLeft hk h _ (subtypeSelf _)
    · exact ih (arrowRight hk h _ (subtypeSelf _)) t ht

theorem select : TypedSubstitutionSelect := by
  intro S K C D f τ k bs es i q ds result values d hk hc hStart hGet hArrow hApp
  obtain ⟨hb, he, _, hBase, hExtra⟩ := parts hStart
  have hQ : InWindow S K C q.type q :=
    hGet.elim (sourceAt (toExtras hb) hBase i) (sourceAt he hExtra i)
  rw [hArrow] at hQ
  have hArgs := NumberedWindowPreservationHeadProof.copies hk hStart k ds (arrowDomains hk ds τ (rootInWindow hQ))
  have hSub := applicationsCommute S K C D ds τ q _ values d hk hc hQ hArgs
  rw [mappedCopies, hApp] at hSub
  refine ⟨?_, annotation (term S K hk values d C D _ _ hQ hc).1, hSub⟩
  rcases hGet with h | h
  · exact .inl (by simp only [mappedGet, h, Option.map_some])
  · exact .inr (by simp only [mappedGet, h, Option.map_some])

end LogicLineages.PersistentMarking.NumberedWindowExternalRawSubstitutionSelectProof
