import LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationOccurrenceProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowSimulationJobs
open Spine (At ArrowPrefix CallTyped)

theorem realizedAt {n qs As i q} (hAt : At qs i q) (h : RealizesArgs n qs As) :
    ∃ Q, As.get i = some Q ∧ Realizes n q Q := by
  induction hAt generalizing As with
  | here =>
    cases h with
    | cons hq _ => exact ⟨_,rfl,hq⟩
  | there _ ih =>
    cases h with
    | cons _ hs =>
      obtain ⟨Q,hGet,hQ⟩ := ih _ hs
      exact ⟨Q,hGet,hQ⟩

theorem getMem (As : NArgs) (i : Nat) (Q : NTerm) (h : As.get i = some Q) :
    Q ∈ As.toList := by
  cases As with
  | nil => cases h
  | cons a rest =>
    cases i with
    | zero =>
      have e : a = Q := Option.some.inj h
      subst Q
      exact List.mem_cons_self
    | succ i =>
      exact List.mem_cons_of_mem _ (getMem rest i Q h)
termination_by i

theorem atValid {S qs i q} (ha : At qs i q) (hs : Spine.ValidArgs S qs) :
    Spine.Valid S q := by
  induction ha with
  | here => exact hs.1
  | there _ ih => exact ih hs.2

theorem paperBaseTypes (C : Spine.BoundContext) (qs : Spine.Args) (ds : List Ty)
    (h : Spine.BaseTyped C qs ds) : types qs = ds := by
  cases qs with
  | nil => cases h; rfl
  | cons q rest =>
    cases h with
    | cons hq hr =>
      simp only [types,SpineShiftProof.annotationExact _ _ _ hq,paperBaseTypes C rest _ hr]
termination_by sizeOf qs

theorem callOwner (f : Head) (τ : Ty) (bs es : Spine.Args) (ds : List Ty)
    (h : Spine.Typed E (.marked f τ bs es) τ) :
    CallTyped E (ArrowPrefix ds τ) (Spine.ownerCopies f bs es ds) τ := by
  cases h with
  | marked hb he =>
    induction ds with
    | nil => exact .nil
    | cons d ds ih => exact .cons (.marked hb he) ih

theorem ownerValid {S f τ bs es} (h : Spine.Valid S (.marked f τ bs es))
    (ds : List Ty) : Spine.ValidArgs S (Spine.ownerCopies f bs es ds) := by
  induction ds with
  | nil => trivial
  | cons d ds ih => exact ⟨h,ih⟩

theorem ownerRealized {n f k bs es Bs Es} (hn : n ≤ k)
    (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) (ds : List Ty) :
    RealizesArgs n (Spine.ownerCopies f bs es ds) (ownerCopies f k Bs Es ds) := by
  induction ds with
  | nil => exact .nil
  | cons d ds ih => exact .cons (.marked hn hb he) ih

theorem appendRealized (n : Nat) (bs es : Spine.Args) (Bs Es : NArgs)
    (hb : RealizesArgs n bs Bs) (he : RealizesArgs n es Es) :
    RealizesArgs n (bs.append es) (Bs.append Es) := by
  cases bs with
  | nil => cases hb; exact he
  | cons q rest =>
    cases hb with
    | cons hq hr => exact .cons hq (appendRealized n rest es _ Es hr he)
termination_by sizeOf bs

end LogicLineages.PersistentMarking.NumberedWindowSimulationOccurrenceProof
