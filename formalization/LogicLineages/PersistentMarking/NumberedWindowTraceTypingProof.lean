import LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets
import LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof

namespace LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPreservationTargets NumberedWindowTraceAlgebra
open NumberedWindowPreservationGuardProof (toExtras)

private def PairType (C : Spine.BoundContext) (τ : Ty) (q r : NTerm) : Prop :=
  Typed C q τ ∧ Typed C r τ

private def PairListType (C : Spine.BoundContext) (types : List Ty) (qs rs : NArgs) : Prop :=
  BaseTyped C qs types ∧ BaseTyped C rs types

theorem primaryEnds {S K C τ q r} (h : Primary S K C τ q r) : PairType C τ q r := by
  induction h using Primary.rec
    (motive_2 := fun C types qs rs _ => PairListType C types qs rs) with
  | refl ht => exact ⟨ht,ht⟩
  | symm _ ih => exact ⟨ih.2,ih.1⟩
  | trans _ _ hq hr => exact ⟨hq.1,hr.2⟩
  | ordinary _ _ _ e hb hc => exact ⟨.ordinary hb,e.symm ▸ Typed.ordinary hc⟩
  | numbered _ _ _ hb hc he => exact ⟨.numbered hb he,.numbered hc he⟩
  | lam _ ih => exact ⟨.lam ih.1,.lam ih.2⟩
  | appFunction _ ha ih => exact ⟨.auxApp ih.1 ha,.auxApp ih.2 ha⟩
  | appArgument hq _ ih => exact ⟨.auxApp hq ih.1,.auxApp hq ih.2⟩
  | ordinaryArguments _ ih => exact ⟨.ordinary ih.1,.ordinary ih.2⟩
  | numberedBase _ he ih => exact ⟨.numbered ih.1 he,.numbered ih.2 he⟩
  | numberedExtras hb _ ih => exact ⟨.numbered hb (toExtras ih.1),.numbered hb (toExtras ih.2)⟩
  | nil => exact ⟨.nil,.nil⟩
  | cons _ _ hq hs => exact ⟨.cons hq.1 hs.1,.cons hq.2 hs.2⟩

private theorem orderedEndsFixed (S : Spine.Signature) (K : List Ty)
    (C : Spine.BoundContext) (types : List Ty) (qs rs : NArgs)
    (h : OrderedPrimary S K C types qs rs) : PairListType C types qs rs := by
  cases qs with
  | nil =>
    cases h with
    | nil => exact ⟨.nil,.nil⟩
  | cons q qs =>
    cases h with
    | cons hq hs =>
      have h1 := primaryEnds hq
      have h2 := orderedEndsFixed S K C _ qs _ hs
      exact ⟨.cons h1.1 h2.1,.cons h1.2 h2.2⟩
termination_by sizeOf qs

theorem orderedEnds {S K C types qs rs} (h : OrderedPrimary S K C types qs rs) :
    PairListType C types qs rs :=
  orderedEndsFixed S K C types qs rs h

theorem orderedRefl (S : Spine.Signature) (K : List Ty) (C : Spine.BoundContext)
    (qs : NArgs) (types : List Ty) (h : BaseTyped C qs types) :
    OrderedPrimary S K C types qs qs := by
  cases qs with
  | nil => cases h; exact .nil
  | cons q qs' =>
    cases h with
    | cons hq hs => exact .cons (.refl hq) (orderedRefl S K C qs' _ hs)
termination_by sizeOf qs

theorem termStart {S K C τ q r} (t : TypedTrace S K C τ q r) : Typed C q τ := by
  cases t with
  | done ht => exact ht
  | raw hq _ _ _ => exact hq
  | equiv he _ => exact (primaryEnds he).1

theorem termEnd {S K C τ q r} (t : TypedTrace S K C τ q r) : Typed C r τ := by
  induction t with
  | done ht => exact ht
  | raw _ _ _ _ ih => exact ih
  | equiv _ _ ih => exact ih

theorem argsStart {S K C types qs rs} (t : ArgsTrace S K C types qs rs) :
    BaseTyped C qs types := by
  cases t with
  | done ht => exact ht
  | raw hq _ _ _ => exact hq
  | equiv he _ => exact (orderedEnds he).1

theorem argsEnd {S K C types qs rs} (t : ArgsTrace S K C types qs rs) :
    BaseTyped C rs types := by
  induction t with
  | done ht => exact ht
  | raw _ _ _ _ ih => exact ih
  | equiv _ _ ih => exact ih

end LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof
