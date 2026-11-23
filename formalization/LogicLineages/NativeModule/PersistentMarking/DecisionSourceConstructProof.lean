module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceBasicProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceConstructProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse DecisionSourceBasicProof

theorem headBuild (K V H Γ f bs) (hd : ∀ τ, τ ∈ declaration f → τ ∈ K)
    (hh : f ∈ H) (hb : ArgsUniverse K V H Γ bs) : Universe K V H Γ (.head f bs) := by
  have h := (argsFacts K V H Γ bs).mp hb
  refine ⟨?_,?_,h.2.2⟩
  · intro τ ht; exact (List.mem_append.mp ht).elim (hd τ) (h.1 τ)
  · intro g hg; exact (List.mem_cons.mp hg).elim (fun he => he ▸ hh) (h.2.1 g)
theorem markedBuild (K V H Γ f τ bs es) (hd : ∀ υ, υ ∈ declaration f → υ ∈ K)
    (ht : ∀ υ, υ ∈ subtypes τ → υ ∈ K) (hh : f ∈ H)
    (hb : ArgsUniverse K V H Γ bs) (he : ArgsUniverse K V H Γ es) : Universe K V H Γ (.marked f τ bs es) := by
  have hb := (argsFacts K V H Γ bs).mp hb
  have he := (argsFacts K V H Γ es).mp he
  refine ⟨?_,?_,?_⟩
  · intro υ hυ; simp only [auxiliarySupport,List.mem_append] at hυ
    rcases hυ with ((h|h)|h)|h
    · exact hd υ h
    · exact ht υ h
    · exact hb.1 υ h
    · exact he.1 υ h
  · intro g hg; simp only [heads,List.mem_cons,List.mem_append] at hg
    rcases hg with h|(h|h)
    · exact h ▸ hh
    · exact hb.2.1 g h
    · exact he.2.1 g h
  · intro n hn; have h : freeOccursArgs n bs = true ∨ freeOccursArgs n es = true := by simpa only [freeOccurs,Bool.or_eq_true] using hn
    exact h.elim (hb.2.2 n) (he.2.2 n)
theorem lamBuild (K V H Γ σ q) (ht : ∀ υ, υ ∈ subtypes (.arrow σ q.type) → υ ∈ K)
    (hσ : ∀ υ, υ ∈ subtypes σ → υ ∈ K) (hq : Universe K V H Γ q) : Universe K V H Γ (.lam σ q) := by
  refine ⟨?_,hq.2.1,hq.2.2⟩
  intro υ hυ; simp only [auxiliarySupport,List.mem_append] at hυ
  exact hυ.elim (fun h => h.elim (ht υ) (hσ υ)) (hq.1 υ)

theorem getUniverse (K V H Γ qs i q) (hu : ArgsUniverse K V H Γ qs) (hi : qs.get i = some q) : Universe K V H Γ q := by
  cases qs with
  | nil => cases i <;> cases hi
  | cons r rs => cases i with
    | zero => simp only [Args.get,Option.some.injEq] at hi; subst q; exact hu.1
    | succ i => exact getUniverse K V H Γ rs i q hu.2 hi
termination_by sizeOf qs

mutual
 theorem shiftFacts (k d : Nat) (q : Expr) : auxiliarySupport (shift k d q) = auxiliarySupport q ∧
    heads (shift k d q) = heads q ∧ (∀ n, freeOccurs n (shift k d q) = freeOccurs n q) := by
  cases q with
  | free σ x => exact ⟨rfl,rfl,fun _ => rfl⟩
  | bound σ i => exact ⟨rfl,rfl,fun _ => rfl⟩
  | lam σ q =>
    obtain ⟨hs,hh,hn⟩ := shiftFacts k (d+1) q
    exact ⟨by simp only [shift,auxiliarySupport,SubstitutionProof.shiftType,hs],hh,hn⟩
  | head f bs =>
    obtain ⟨hs,hh,hn⟩ := shiftFactsArgs k d bs
    exact ⟨by simp only [shift,auxiliarySupport,hs],by simp only [shift,heads,hh],hn⟩
  | marked f τ bs es =>
    obtain ⟨hs,hh,hn⟩ := shiftFactsArgs k d bs
    obtain ⟨hs',hh',hn'⟩ := shiftFactsArgs k d es
    exact ⟨by simp only [shift,auxiliarySupport,hs,hs'],by simp only [shift,heads,hh,hh'],fun n => by simp only [shift,freeOccurs,hn n,hn' n]⟩
 termination_by sizeOf q
 theorem shiftFactsArgs (k d : Nat) (qs : Args) : auxiliaryArgs (shiftArgs k d qs) = auxiliaryArgs qs ∧
    headsArgs (shiftArgs k d qs) = headsArgs qs ∧ (∀ n, freeOccursArgs n (shiftArgs k d qs) = freeOccursArgs n qs) := by
  cases qs with
  | nil => exact ⟨rfl,rfl,fun _ => rfl⟩
  | cons q qs =>
    obtain ⟨hs,hh,hn⟩ := shiftFacts k d q
    obtain ⟨hs',hh',hn'⟩ := shiftFactsArgs k d qs
    exact ⟨by simp only [shiftArgs,auxiliaryArgs,hs,hs'],by simp only [shiftArgs,headsArgs,hh,hh'],fun n => by simp only [shiftArgs,freeOccursArgs,hn n,hn' n]⟩
 termination_by sizeOf qs
end

theorem shiftUniverse (K V H Γ k d q) (hu : Universe K V H Γ q) : Universe K V H Γ (shift k d q) := by
  obtain ⟨hs,hh,hn⟩ := shiftFacts k d q
  exact ⟨fun σ h => hu.1 σ (hs ▸ h),fun f h => hu.2.1 f (hh ▸ h),fun n h => hu.2.2 n ((hn n) ▸ h)⟩
end LogicLineages.PersistentMarking.DecisionSourceConstructProof
