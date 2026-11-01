module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsStructureProof
public import LogicLineages.OrdinalComparison.CollectedNormalizeProof
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads

private theorem tags_tail_induction {P : CollectedPositiveTags → Prop}
    (nil : P .nil)
    (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : CollectedPositiveTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (tags_tail_induction nil cons rest)
termination_by tags

private theorem insert_origins (rho : NONote) (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags) :
    ∀ p∈collectedDirectTags (collectedTagInsert rho A a tags),p=(rho,A) ∨ p∈collectedDirectTags tags := by
  induction tags using tags_tail_induction with
  | nil =>
    intro p hp
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,collectedDirectTags] at hp
    · simp only [collectedTagInsert,if_neg ha,collectedDirectTags,List.mem_cons,List.not_mem_nil,or_false] at hp
      exact Or.inl hp
  | cons sigma B b rest ih =>
    intro p hp
    by_cases ha : a=0
    · exact Or.inr (by simpa only [collectedTagInsert,if_pos ha] using hp)
    · by_cases hlt : collectedTagKey rho A<collectedTagKey sigma B
      · simp only [collectedTagInsert,if_neg ha,if_pos hlt,collectedDirectTags,List.mem_cons] at hp
        simpa only [collectedDirectTags,List.mem_cons] using hp
      · by_cases heq : collectedTagKey rho A=collectedTagKey sigma B
        · exact Or.inr (by simpa only [collectedTagInsert,if_neg ha,if_neg hlt,if_pos heq,collectedDirectTags] using hp)
        · simp only [collectedTagInsert,if_neg ha,if_neg hlt,if_neg heq,collectedDirectTags,List.mem_cons] at hp
          rcases hp with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · rcases ih p h with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)

private theorem merge_origins (left right : CollectedPositiveTags) :
    ∀ p∈collectedDirectTags (collectedTagsMerge left right),
      p∈collectedDirectTags left ∨ p∈collectedDirectTags right := by
  induction left using tags_tail_induction with
  | nil => intro p hp; exact Or.inr hp
  | cons rho A a rest ih =>
    intro p hp
    rcases insert_origins rho A a (collectedTagsMerge rest right) p hp with h | h
    · exact Or.inl (List.mem_cons.mpr (Or.inl h))
    · rcases ih p h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem root_provenance : Targets.CollectedRootRawSourceProvenance := by
  intro E
  induction E with
  | constant n =>
    intro _ rho A h
    cases h
  | input =>
    intro _ rho A h
    cases h
  | add E F ihE ihF =>
    intro hv rho A h
    cases hE : collectedPositiveNormalize E with
    | mk c b tags =>
      cases hF : collectedPositiveNormalize F with
      | mk d e rest =>
        have hm : (rho,A)∈collectedDirectTags (collectedTagsMerge tags rest) := by
          simpa only [collectedPositiveNormalize,hE,hF,collectedPositiveAdd,collectedSourceRootTags] using h
        rcases merge_origins tags rest (rho,A) hm with hm | hm
        · obtain ⟨raw,hraw,hnorm⟩ := ihE hv.1 rho A (by simpa only [hE,collectedSourceRootTags] using hm)
          exact ⟨raw,List.mem_append_left _ hraw,hnorm⟩
        · obtain ⟨raw,hraw,hnorm⟩ := ihF hv.2 rho A (by simpa only [hF,collectedSourceRootTags] using hm)
          exact ⟨raw,List.mem_append_right _ hraw,hnorm⟩
  | head sigma E ih =>
    intro hv rho A h
    by_cases hc : collectedPositiveSupport (collectedPositiveNormalize E)=false
    · simp only [collectedPositiveNormalize,if_pos hc,collectedSourceRootTags,collectedDirectTags] at h
      cases h
    · have hopen : collectedPositiveSupport (collectedPositiveNormalize E)=true := by
        cases hs : collectedPositiveSupport (collectedPositiveNormalize E) <;> simp_all
      have hinput : positiveExprHasInput E=true := (collectedPositiveNormalizeSupport E hv.2.2).symm.trans hopen
      have heq : (rho,A)=(sigma,collectedPositiveNormalize E) := by
        simpa only [collectedPositiveNormalize,if_neg hc,collectedSourceRootTags,collectedDirectTags,
          List.mem_cons,List.not_mem_nil,or_false] using h
      obtain ⟨hR,hA⟩ := Prod.mk.inj heq
      subst rho A
      refine ⟨E,?_,rfl⟩
      simp only [comparisonDisplayedSourceHeads,if_pos hinput,List.mem_singleton]

private theorem row_origins (A B : CollectedPositiveNF) (hA : CollectedPositiveValid A) (hB : CollectedPositiveValid B) :
    ∀ entry∈(signedCollectedNFRow A B).2.2,
      entry.1∈collectedSourceRootTags A ∨ entry.1∈collectedSourceRootTags B := by
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      exact (signedCollectedDifferenceValid tags rest hA hB).2

theorem signed_argument_drop : Targets.SignedRowRawSourceArgumentDrop := by
  intro E F hE hF
  dsimp only
  let row := (signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2
  have hrow := row_origins (collectedPositiveNormalize E) (collectedPositiveNormalize F)
    (collectedPositiveNormalizeValid E hE) (collectedPositiveNormalizeValid F hF)
  have hall : ∀ entry∈row,∃ raw : FixedLimitPositiveExpr,
      (entry.1.1,raw)∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F ∧
      collectedPositiveNormalize raw=entry.1.2 := by
    intro entry hentry
    rcases hrow entry hentry with h | h
    · obtain ⟨raw,hr,hn⟩ := root_provenance E hE entry.1.1 entry.1.2 h
      exact ⟨raw,List.mem_append_left _ hr,hn⟩
    · obtain ⟨raw,hr,hn⟩ := root_provenance F hF entry.1.1 entry.1.2 h
      exact ⟨raw,List.mem_append_right _ hr,hn⟩
  refine ⟨hall,?_⟩
  intro a ha b hb hkey
  obtain ⟨rawA,hrawA,hnormA⟩ := hall a ha
  obtain ⟨rawB,hrawB,hnormB⟩ := hall b hb
  have hne : (a.1.1,rawA)≠(b.1.1,rawB) := by
    intro heq
    have hr : a.1.1=b.1.1 := congrArg (fun p : NONote × FixedLimitPositiveExpr => p.1) heq
    have hraw : rawA=rawB := congrArg (fun p : NONote × FixedLimitPositiveExpr => p.2) heq
    apply hkey
    rw [← hnormA,← hnormB,hr,hraw]
  exact ⟨rawA,rawB,hrawA,hrawB,hnormA,hnormB,
    argument_drop.2 E F (a.1.1,rawA) (b.1.1,rawB) hrawA hrawB hne⟩

end LogicLineages.OrdinalComparison.SourceDisplayedHeads
