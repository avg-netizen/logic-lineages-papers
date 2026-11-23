module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceBudgetTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowOrdinaryQuoteProof
open NumberedWindowSyntax NumberedWindowOrdinaryTranslation NumberedWindowTupleTargets

mutual
theorem term (q : Spine.Expr) (Q : NTerm) (h : tr q = some Q) :
    Spine.Ordinary q ∧ ∀ n, Realizes n q Q ∧ ∀ R, Realizes n q R → R = Q := by
  cases q with
  | free σ x =>
    have e : NTerm.free σ x = Q := Option.some.inj h
    subst Q
    exact ⟨True.intro,fun n => ⟨.free,fun R hr => by cases hr; rfl⟩⟩
  | bound σ i =>
    have e : NTerm.bound σ i = Q := Option.some.inj h
    subst Q
    exact ⟨True.intro,fun n => ⟨.bound,fun R hr => by cases hr; rfl⟩⟩
  | lam σ q =>
    cases hq : tr q with
    | none => simp [tr,hq] at h
    | some out =>
      have e : NTerm.lam σ out = Q := by simpa only [tr,hq,Option.map_some,Option.some.injEq] using h
      subst Q
      obtain ⟨ho,hb⟩ := term q out hq
      refine ⟨ho,fun n => ⟨.lam (hb n).1,?_⟩⟩
      intro R hr
      cases hr with
      | lam hr => exact congrArg (NTerm.lam σ) ((hb n).2 _ hr)
  | head f bs =>
    cases hb : trArgs bs with
    | none => simp [tr,hb] at h
    | some args =>
      have e : NTerm.ordinary f args = Q := by simpa only [tr,hb,Option.map_some,Option.some.injEq] using h
      subst Q
      obtain ⟨ho,hargs⟩ := list bs args hb
      refine ⟨ho,fun n => ⟨.ordinary (hargs n).1,?_⟩⟩
      intro R hr
      cases hr with
      | ordinary hr => exact congrArg (NTerm.ordinary f) ((hargs n).2 _ hr)
  | marked f τ bs es => simp [tr] at h
termination_by sizeOf q

theorem list (bs : Spine.Args) (As : NArgs) (h : trArgs bs = some As) :
    Spine.OrdinaryArgs bs ∧ ∀ n, RealizesArgs n bs As ∧ ∀ Bs, RealizesArgs n bs Bs → Bs = As := by
  cases bs with
  | nil =>
    have e : NArgs.nil = As := Option.some.inj h
    subst As
    exact ⟨True.intro,fun n => ⟨.nil,fun R hr => by cases hr; rfl⟩⟩
  | cons q qs =>
    cases hq : tr q with
    | none => simp [trArgs,hq] at h
    | some out =>
      cases hs : trArgs qs with
      | none => simp [trArgs,hq,hs] at h
      | some rest =>
        have e : NArgs.cons out rest = As := by simpa [trArgs,hq,hs] using h
        subst As
        obtain ⟨ho,hterm⟩ := term q out hq
        obtain ⟨hos,htail⟩ := list qs rest hs
        refine ⟨⟨ho,hos⟩,fun n => ⟨.cons (hterm n).1 (htail n).1,?_⟩⟩
        intro Bs hBs
        cases hBs with
        | cons hFirst hTail =>
          rw [(hterm n).2 _ hFirst,(htail n).2 _ hTail]
termination_by sizeOf bs
end

end LogicLineages.PersistentMarking.NumberedWindowOrdinaryQuoteProof
