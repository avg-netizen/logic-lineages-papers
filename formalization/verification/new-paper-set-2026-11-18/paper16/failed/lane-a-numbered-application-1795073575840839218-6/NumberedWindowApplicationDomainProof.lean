import LogicLineages.PersistentMarking.NumberedWindowApplicationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowApplicationTargets
open TypeSupport (subtypes)
open DecisionInventory (declaration)

theorem annotation {C : Spine.BoundContext} {Q : NTerm} {τ : Ty} (h : Typed C Q τ) :
    Q.type = τ := by
  cases h with
  | free => rfl
  | bound h => rfl
  | lam h => simp only [NTerm.type,annotation h]
  | bottom => rfl
  | ordinary h => rfl
  | numbered hb he => rfl
  | auxApp hq ha => rfl
termination_by sizeOf Q

theorem subtypeSelf (τ : Ty) : τ ∈ subtypes τ := by
  cases τ <;> exact List.mem_cons_self

theorem rootSupport (Q : NTerm) : Q.type ∈ support Q := by
  cases Q with
  | free σ x => exact subtypeSelf σ
  | bound σ i => exact subtypeSelf σ
  | bottom τ => exact subtypeSelf τ
  | lam σ Q => exact List.mem_append_left _ (List.mem_append_left _ (subtypeSelf _))
  | ordinary f bs => exact List.mem_append_left _ (List.mem_append_left _ (subtypeSelf _))
  | numbered f τ k bs es =>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (subtypeSelf _)))
  | auxApp σ τ Q A =>
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (subtypeSelf _)))

theorem rootInWindow {S : Spine.Signature} {K : List Ty} {C : Spine.BoundContext} {τ : Ty} {Q : NTerm}
    (h : InWindow S K C τ Q) : τ ∈ K :=
  annotation h.1 ▸ h.2.1 Q.type (rootSupport Q)

theorem arrowLeft {K : List Ty} {σ τ : Ty} (hk : DecisionSourceUniverse.Closed K)
    (h : Ty.arrow σ τ ∈ K) (ρ : Ty) (hρ : ρ ∈ subtypes σ) : ρ ∈ K :=
  hk _ h ρ (List.mem_cons_of_mem _ (List.mem_append_left _ hρ))

theorem arrowRight {K : List Ty} {σ τ : Ty} (hk : DecisionSourceUniverse.Closed K)
    (h : Ty.arrow σ τ ∈ K) (ρ : Ty) (hρ : ρ ∈ subtypes τ) : ρ ∈ K :=
  hk _ h ρ (List.mem_cons_of_mem _ (List.mem_append_right _ hρ))

theorem app : AppInWindow := by
  intro S K C σ τ Q A hk hQ hA
  have hRoot := rootInWindow hQ
  refine ⟨.auxApp hQ.1 hA.1,?_,?_⟩
  · intro ρ h
    simp only [support,List.mem_append] at h
    rcases h with ((hτ | hσ) | hq) | ha
    · exact arrowRight hk hRoot ρ hτ
    · exact arrowLeft hk hRoot ρ hσ
    · exact hQ.2.1 ρ hq
    · exact hA.2.1 ρ ha
  · intro f h
    simp only [heads,List.mem_append] at h
    exact h.elim (hQ.2.2 f) (hA.2.2 f)

theorem appEq {C : Spine.BoundContext} {σ τ : Ty} {Q A : NTerm}
    (hQ : Typed C Q (.arrow σ τ)) (hA : Typed C A σ) (As : NArgs) :
    applications Q (.cons A As) = applications (.auxApp σ τ Q A) As := by
  simp only [applications,annotation hQ,annotation hA,if_true]

end LogicLineages.PersistentMarking.NumberedWindowApplicationDomainProof
