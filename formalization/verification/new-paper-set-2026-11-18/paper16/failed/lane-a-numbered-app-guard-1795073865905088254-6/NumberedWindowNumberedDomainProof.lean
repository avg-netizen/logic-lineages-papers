import LogicLineages.PersistentMarking.NumberedWindowApplicationShiftProof

namespace LogicLineages.PersistentMarking.NumberedWindowNumberedDomainProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowApplicationTargets
open NumberedWindowApplicationDomainProof
open TypeSupport (subtypes)
open DecisionInventory (declaration)

def ArgsGuard (S : Spine.Signature) (K : List Ty) (As : NArgs) : Prop :=
  (∀ ρ, ρ ∈ argsSupport As → ρ ∈ K) ∧
    ∀ g, g ∈ argsHeads As → HeadInWindow S K g

theorem parts {S : Spine.Signature} {K : List Ty} {C : Spine.BoundContext}
    {f : Head} {τ : Ty} {k : Nat} {bs es : NArgs}
    (h : InWindow S K C τ (.numbered f τ k bs es)) :
    BaseTyped C bs f.arguments ∧ ExtrasTyped C es ∧ HeadInWindow S K f ∧
      ArgsGuard S K bs ∧ ArgsGuard S K es := by
  have ht : BaseTyped C bs f.arguments ∧ ExtrasTyped C es := by
    cases h.1 with
    | numbered hb he => exact ⟨hb,he⟩
  refine ⟨ht.1,ht.2,h.2.2 f List.mem_cons_self,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro ρ hρ
    exact h.2.1 ρ (List.mem_append_left _ (List.mem_append_right _ hρ))
  · intro g hg
    exact h.2.2 g (List.mem_cons_of_mem _ (List.mem_append_left _ hg))
  · intro ρ hρ
    exact h.2.1 ρ (List.mem_append_right _ hρ)
  · intro g hg
    exact h.2.2 g (List.mem_cons_of_mem _ (List.mem_append_right _ hg))

theorem numbered {S : Spine.Signature} {K : List Ty} {C : Spine.BoundContext}
    {f : Head} {τ : Ty} {k : Nat} {bs es : NArgs}
    (hb : BaseTyped C bs f.arguments) (he : ExtrasTyped C es) (hf : HeadInWindow S K f)
    (ht : ∀ ρ, ρ ∈ subtypes τ → ρ ∈ K)
    (hBs : ArgsGuard S K bs) (hEs : ArgsGuard S K es) :
    InWindow S K C τ (.numbered f τ k bs es) := by
  refine ⟨.numbered hb he,?_,?_⟩
  · intro ρ h
    simp only [support,List.mem_append] at h
    rcases h with ((hd | hτ) | hb) | he
    · exact hf.2 ρ hd
    · exact ht ρ hτ
    · exact hBs.1 ρ hb
    · exact hEs.1 ρ he
  · intro g h
    simp only [heads,List.mem_cons,List.mem_append] at h
    rcases h with rfl | hb | he
    · exact hf
    · exact hBs.2 g hb
    · exact hEs.2 g he

theorem shiftedGuard {S : Spine.Signature} {K : List Ty} {As : NArgs}
    (h : ArgsGuard S K As) (a c : Nat) : ArgsGuard S K (shiftArgs a c As) := by
  rcases NumberedWindowApplicationShiftProof.argsShape As a c with ⟨hs,hh⟩
  exact ⟨fun ρ hp => h.1 ρ (hs ▸ hp),fun f hp => h.2 f (hh ▸ hp)⟩

theorem extrasAppend {C : Spine.BoundContext} {As Bs : NArgs}
    (hA : ExtrasTyped C As) (hB : ExtrasTyped C Bs) : ExtrasTyped C (As.append Bs) := by
  cases hA with
  | nil => exact hB
  | cons hq htail => exact .cons hq (extrasAppend htail hB)
termination_by sizeOf As

theorem appendOneGuard {S : Spine.Signature} {K : List Ty} {C : Spine.BoundContext}
    {As : NArgs} {A : NTerm} {σ : Ty}
    (hAs : ArgsGuard S K As) (hA : InWindow S K C σ A) :
    ArgsGuard S K (As.append (.cons A .nil)) := by
  cases As with
  | nil =>
    refine ⟨?_,?_⟩
    · intro t ht
      exact hA.2.1 t (by simpa only [NArgs.append,argsSupport,List.append_nil] using ht)
    · intro f hf
      exact hA.2.2 f (by simpa only [NArgs.append,argsHeads,List.append_nil] using hf)
  | cons b rest =>
    have hRest : ArgsGuard S K rest :=
      ⟨fun ρ h => hAs.1 ρ (List.mem_append_right _ h),
        fun f h => hAs.2 f (List.mem_append_right _ h)⟩
    have ih := appendOneGuard hRest hA
    refine ⟨?_,?_⟩
    · intro ρ hρ
      simp only [NArgs.append,argsSupport,List.mem_append] at hρ
      exact hρ.elim (fun hb => hAs.1 ρ (List.mem_append_left _ hb)) (ih.1 ρ)
    · intro f hf
      simp only [NArgs.append,argsHeads,List.mem_append] at hf
      exact hf.elim (fun hb => hAs.2 f (List.mem_append_left _ hb)) (ih.2 f)
termination_by sizeOf As

theorem appendArg : AppendArgumentInWindow := by
  intro S K C f σ τ k bs es A hk hOwn hA
  obtain ⟨hb,he,hf,hbs,hes⟩ := parts hOwn
  exact numbered hb (extrasAppend he (.cons hA.1 .nil)) hf
    (arrowRight hk (rootInWindow hOwn)) hbs (appendOneGuard hes hA)

theorem openNumberedWindow : OpenNumberedInWindow := by
  intro S K C f σ τ k bs es hk hOwn
  obtain ⟨hb,he,hf,hbs,hes⟩ := parts hOwn
  let D := C.push σ
  have hc := SpineShiftProof.compatibleOne C σ
  have hb' := NumberedWindowApplicationShiftProof.baseTyped C D bs _ 1 0 hb hc
  have he' := NumberedWindowApplicationShiftProof.extrasTyped C D es 1 0 he hc
  have hroot := rootInWindow hOwn
  have hBound : InWindow S K D σ (.bound σ 0) :=
    ⟨.bound rfl,arrowLeft hk hroot,fun _ h => False.elim (List.not_mem_nil h)⟩
  have hBody : InWindow S K D τ (openNumbered f σ τ k bs es) := by
    exact numbered hb' (extrasAppend he' (.cons hBound.1 .nil)) hf
      (arrowRight hk hroot) (shiftedGuard hbs 1 0)
      (appendOneGuard (shiftedGuard hes 1 0) hBound)
  refine ⟨.lam hBody.1,?_,hBody.2.2⟩
  intro ρ h
  simp only [support,List.mem_append,openNumbered,NTerm.type] at h
  rcases h with (hArrow | hσ) | hb
  · exact hk _ hroot ρ hArrow
  · exact arrowLeft hk hroot ρ hσ
  · exact hBody.2.1 ρ hb

end LogicLineages.PersistentMarking.NumberedWindowNumberedDomainProof
