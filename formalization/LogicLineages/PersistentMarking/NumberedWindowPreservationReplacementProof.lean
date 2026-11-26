import LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationReplacementProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowPreservationGuardProof
open NumberedWindowApplicationDomainProof (rootSupport)
open NumberedWindowNumberedDomainProof (ArgsGuard)
open TypeSupport (subtypes)

theorem every {S K} (qs : NArgs) :
    ArgsGuard S K qs ↔ ∀ q ∈ qs.toList, TermGuard S K q := by
  cases qs with
  | nil =>
    exact ⟨fun _ _ h => False.elim (List.not_mem_nil h),fun _ => nilGuard⟩
  | cons q qs =>
    constructor
    · intro h x hx
      have parts := consParts h
      change x ∈ q :: qs.toList at hx
      rcases List.mem_cons.mp hx with rfl | ht
      · exact parts.1
      · exact (every qs).mp parts.2 x ht
    · intro h
      exact consGuard (h q List.mem_cons_self)
        ((every qs).mpr (fun x hx => h x (List.mem_cons_of_mem _ hx)))
termination_by sizeOf qs

theorem permGuard {S K qs rs} (hp : qs.toList.Perm rs.toList)
    (h : ArgsGuard S K qs) : ArgsGuard S K rs :=
  (every rs).mpr (fun q hq => (every qs).mp h q (hp.mem_iff.mpr hq))

theorem decrease {S K b a}
    (hk : DecisionSourceUniverse.Closed K) (hd : MarkDecrease b a) :
    a.type = b.type ∧ (TermGuard S K b → TermGuard S K a) := by
  induction hd with
  | omega =>
    rename_i f bs k
    refine ⟨rfl,?_⟩
    intro h
    refine ⟨?_,?_⟩
    · intro τ hτ
      simp only [support,argsSupport,List.append_nil,List.mem_append] at hτ
      rcases hτ with (hd | hr) | hb
      · exact h.1 τ (List.mem_append_left _ hd)
      · exact hk _ (h.1 _ (rootSupport (.ordinary f bs))) τ hr
      · exact h.1 τ (List.mem_append_right _ hb)
    · intro g hg
      exact h.2 g (by simpa only [heads,argsHeads,List.append_nil] using hg)
  | finite _ =>
    exact ⟨rfl,fun h => h⟩
  | lam _ ih =>
    refine ⟨by simp only [NTerm.type,ih.1],?_⟩
    intro h
    refine ⟨?_,?_⟩
    · intro τ hτ
      simp only [support,NTerm.type,ih.1,List.mem_append] at hτ
      rcases hτ with (hr | hσ) | hb
      · exact h.1 τ (List.mem_append_left _ (List.mem_append_left _ hr))
      · exact h.1 τ (List.mem_append_left _ (List.mem_append_right _ hσ))
      · exact (ih.2 ⟨fun t ht => h.1 t (List.mem_append_right _ ht),h.2⟩).1 τ hb
    · exact (ih.2 ⟨fun t ht => h.1 t (List.mem_append_right _ ht),h.2⟩).2

theorem replacement {S K bs target}
    (hk : DecisionSourceUniverse.Closed K) (h : ArgsGuard S K bs)
    (hp : PrimitiveReplacement bs target) : ArgsGuard S K target := by
  obtain ⟨kept,removed,added,hSrc,hTgt,_nonempty,hOrigin⟩ := hp
  apply (every target).mpr
  intro q hq
  have hs := (every bs).mp h
  rcases List.mem_append.mp (hTgt.mem_iff.mp hq) with hKept | hAdded
  · exact hs q (hSrc.mem_iff.mpr (List.mem_append_left _ hKept))
  · obtain ⟨b,hb,hd⟩ := hOrigin q hAdded
    exact (decrease hk hd).2 (hs b (hSrc.mem_iff.mpr (List.mem_append_right _ hb)))

end LogicLineages.PersistentMarking.NumberedWindowPreservationReplacementProof
