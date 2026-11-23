module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineSoundStageTargets
public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceBasicProof
public import LogicLineages.NativeModule.PersistentMarking.SpineCallTypingProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundSourceProof
open Spine DecisionInventory DecisionPorts PortNormalization
open ProtectedSpineAdequacyTargets

def ExprValid (S : Signature) (q : Expr) : Prop :=
  Valid S q ↔ ∀ f, f ∈ heads q → Admitted S f

private def ArgsValid (S : Signature) (args : Args) : Prop :=
  ValidArgs S args ↔ ∀ f, f ∈ headsArgs args → Admitted S f

theorem checkHeads (S : Signature) (q : Expr) : ExprValid S q := by
  apply @Expr.rec (ExprValid S) (ArgsValid S)
  · intro σ x
    simp [ExprValid,Valid,heads]
  · intro σ i
    simp [ExprValid,Valid,heads]
  · intro σ q h
    exact h
  · intro f bs hb
    simp only [ExprValid,ArgsValid,Valid,heads,List.mem_cons] at hb ⊢
    rw [hb]
    constructor
    · intro h g hg
      rcases hg with rfl | hg
      · exact h.1
      · exact h.2 g hg
    · intro h
      exact ⟨h _ (Or.inl rfl),fun _ hg => h _ (Or.inr hg)⟩
  · intro f τ bs es hb he
    simp only [ExprValid,ArgsValid,Valid,heads,List.mem_cons,List.mem_append] at hb he ⊢
    rw [hb,he]
    constructor
    · intro h g hg
      rcases hg with rfl | hg | hg
      · exact h.1
      · exact h.2.1 g hg
      · exact h.2.2 g hg
    · intro h
      exact ⟨h _ (Or.inl rfl),fun _ hg => h _ (Or.inr (Or.inl hg)),
        fun _ hg => h _ (Or.inr (Or.inr hg))⟩
  · simp [ArgsValid,ValidArgs,headsArgs]
  · intro q args hq ha
    simp only [ExprValid,ArgsValid,ValidArgs,headsArgs,List.mem_append] at hq ha ⊢
    rw [hq,ha]
    constructor
    · intro h f hf
      exact hf.elim (h.1 f) (h.2 f)
    · intro h
      exact ⟨fun f hf => h f (Or.inl hf),fun f hf => h f (Or.inr hf)⟩

theorem validSource (F : Inputs S) (Γ : Context) (q : Expr) (h : Source F Γ q) : Valid S q :=
  (checkHeads S q).mpr (fun f hf => (checkHeads S F.source).mp F.sourcePaper.2 f (h.2.1 f hf))

theorem atTyped {Γ : BoundContext} {args : Args} {i : Nat} {q : Expr} (ha : At args i q)
    (ht : ExtrasTyped Γ args) : Typed Γ q q.type := by
  induction ha with
  | here =>
    cases ht with
    | cons h _ =>
      have he := SpineShiftProof.annotationExact _ _ _ h
      exact he.symm ▸ h
  | there _ ih =>
    cases ht with
    | cons _ h => exact ih h

theorem atAppendLeft {xs ys : Args} {i : Nat} {q : Expr} (h : At xs i q) :
    At (xs.append ys) i q := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem atAppendRight (xs : Args) {ys : Args} {i : Nat} {q : Expr} (h : At ys i q) :
    ∃ j, At (xs.append ys) j q := by
  cases xs with
  | nil => exact ⟨i,h⟩
  | cons a xs =>
    obtain ⟨j,hj⟩ := atAppendRight xs h
    exact ⟨j+1,.there hj⟩
termination_by sizeOf xs

theorem atCall {τ : Ty} {ds : List Ty} {args : Args}
    (ht : CallTyped EmptyContext (ArrowPrefix ds τ) args τ)
    {i : Nat} {ρ : Ty} (hi : ds[i]? = some ρ) :
    ∃ q, At args i q ∧ q.type = ρ := by
  induction ds generalizing args i with
  | nil => simp at hi
  | cons d ds ih =>
    generalize hStart : ArrowPrefix (d::ds) τ = start at ht
    cases ht with
    | nil =>
      have hn := (FinitePrefixProof.proper _ _ _ (FinitePrefixProof.backward (d::ds) τ (by simp))).1
      rw [hStart] at hn
      omega
    | @cons q σ restType tail _ hq hrest =>
      obtain ⟨hDom,hTail⟩ := Ty.arrow.inj hStart
      cases i with
      | zero =>
        have he : d = ρ := by simpa using hi
        exact ⟨_,.here,(SpineShiftProof.annotationExact _ _ _ hq).trans (hDom.symm.trans he)⟩
      | succ i =>
        obtain ⟨q,ha,he⟩ := ih (hTail.symm ▸ hrest) (by simpa using hi)
        exact ⟨q,.there ha,he⟩

end LogicLineages.PersistentMarking.ProtectedSpineSoundSourceProof
