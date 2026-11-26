module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTypingBitsArgsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsCasesProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTypingBits
open NumberedWindowTypingBitsArgsProof
open NumberedWindowApplicationDomainProof (annotation)

abbrev TermGoal (Q : NTerm) : Prop :=
  ∀ C, termOK C Q = true ↔ Typed C Q Q.type

abbrev ArgsGoal (qs : NArgs) : Prop :=
  ∀ C, argsOK C qs = true ↔ BaseTyped C qs (annotationList qs)

theorem freeCase (σ : Ty) (x : Nat) : TermGoal (.free σ x) := by
  intro C
  exact ⟨fun _ => .free,fun _ => rfl⟩

theorem boundCase (σ : Ty) (i : Nat) : TermGoal (.bound σ i) := by
  intro C
  simp only [termOK,decide_eq_true_eq,NTerm.type]
  exact ⟨Typed.bound,fun h => by cases h with | bound hb => exact hb⟩

theorem lamCase (σ : Ty) (Q : NTerm) (iq : TermGoal Q) :
    TermGoal (.lam σ Q) := by
  intro C
  simp only [termOK,iq,NTerm.type]
  exact ⟨Typed.lam,fun h => by cases h with | lam hq => exact hq⟩

theorem bottomCase (σ : Ty) : TermGoal (.bottom σ) := by
  intro C
  exact ⟨fun _ => .bottom,fun _ => rfl⟩

theorem ordinaryCase (f : Head) (qs : NArgs) (iq : ArgsGoal qs) :
    TermGoal (.ordinary f qs) := by
  intro C
  simp only [termOK,Bool.and_eq_true,decide_eq_true_eq,iq,NTerm.type]
  constructor
  · rintro ⟨e,h⟩
    exact .ordinary (e ▸ h)
  · intro h
    cases h with
    | ordinary hb =>
      have e := (baseShape hb).1
      exact ⟨e,e.symm ▸ hb⟩

theorem numberedCase (f : Head) (τ : Ty) (k : Nat) (bs es : NArgs)
    (ib : ArgsGoal bs) (ie : ArgsGoal es) : TermGoal (.numbered f τ k bs es) := by
  intro C
  simp only [termOK,Bool.and_eq_true,decide_eq_true_eq,ib,ie,NTerm.type]
  constructor
  · rintro ⟨⟨e,hb⟩,he⟩
    exact .numbered (e ▸ hb) (baseShape he).2
  · intro h
    cases h with
    | numbered hb he =>
      have e := (baseShape hb).1
      exact ⟨⟨e,e.symm ▸ hb⟩,extrasBase he⟩

theorem auxCase (σ τ : Ty) (Q A : NTerm) (iq : TermGoal Q) (ia : TermGoal A) :
    TermGoal (.auxApp σ τ Q A) := by
  intro C
  simp only [termOK,Bool.and_eq_true,decide_eq_true_eq,iq,ia,NTerm.type]
  constructor
  · rintro ⟨⟨⟨eQ,hq⟩,eA⟩,ha⟩
    exact .auxApp (eQ ▸ hq) (eA ▸ ha)
  · intro h
    cases h with
    | auxApp hq ha =>
      have eQ := annotation hq
      have eA := annotation ha
      exact ⟨⟨⟨eQ,eQ.symm ▸ hq⟩,eA⟩,eA.symm ▸ ha⟩

theorem nilCase : ArgsGoal .nil := by
  intro C
  exact ⟨fun _ => .nil,fun _ => rfl⟩

theorem consCase (Q : NTerm) (qs : NArgs) (iq : TermGoal Q) (ia : ArgsGoal qs) :
    ArgsGoal (.cons Q qs) := by
  intro C
  simp only [argsOK,Bool.and_eq_true,iq,ia]
  constructor
  · rintro ⟨hq,ha⟩
    exact .cons hq ha
  · intro h
    cases h with
    | cons hq ha => exact ⟨hq,ha⟩

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsCasesProof
