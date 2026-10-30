module
public import LogicLineages.OrdinalComparison.CollectedMergeTargets
public import LogicLineages.OrdinalComparison.CollectedPositiveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem tags_tail_induction {P : CollectedPositiveTags → Prop}
    (nil : P .nil)
    (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : CollectedPositiveTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (tags_tail_induction nil cons rest)
termination_by tags


private theorem keys_above_mono (tags : CollectedPositiveTags) {j k : Nat}
    (hjk : j≤k) (h : collectedTagsKeysAbove k tags) : collectedTagsKeysAbove j tags := by
  induction tags using tags_tail_induction with
  | nil => trivial
  | cons rho A a rest ih => exact ⟨hjk.trans_lt h.1,ih h.2⟩

private theorem insert_keys_above (rho : NONote) (A : CollectedPositiveNF) (a k : Nat)
    (tags : CollectedPositiveTags) (hk : k<collectedTagKey rho A)
    (ht : collectedTagsKeysAbove k tags) :
    collectedTagsKeysAbove k (collectedTagInsert rho A a tags) := by
  induction tags using tags_tail_induction with
  | nil =>
    simp only [collectedTagInsert]
    split
    · trivial
    · exact ⟨hk,True.intro⟩
  | cons sigma B b rest ih =>
    simp only [collectedTagInsert]
    split
    · exact ht
    split
    · exact ⟨hk,ht⟩
    split
    · exact ht
    · exact ⟨ht.1,ih ht.2⟩

theorem collectedTagInsertValue : Targets.CollectedTagInsertValue := by
  intro rho A a tags x
  induction tags using tags_tail_induction with
  | nil =>
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,actualCollectedTagsEval]
    · simp [collectedTagInsert,ha,actualCollectedTagsEval]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,actualCollectedTagsEval]
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · simp [collectedTagInsert,ha,hl,actualCollectedTagsEval]
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨rfl,rfl⟩
      simp [collectedTagInsert,ha,actualCollectedTagsEval,Nat.add_mul,Nat.add_assoc]
    · simp only [collectedTagInsert,if_neg ha,if_neg hl,if_neg he,actualCollectedTagsEval,ih]
      omega

theorem collectedTagInsertValid : Targets.CollectedTagInsertValid := by
  intro rho A a tags hr he hA ho ht
  induction tags using tags_tail_induction with
  | nil =>
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,CollectedTagsValid]
    · simp only [collectedTagInsert,if_neg ha]
      exact ⟨hr,he,hA,ho,Nat.pos_of_ne_zero ha,True.intro,True.intro⟩
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simpa only [collectedTagInsert,if_pos ha] using ht
    rcases ht with ⟨hs,hse,hB,hBo,hb,hkeys,hrest⟩
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · rw [collectedTagInsert,if_neg ha,if_pos hl]
      exact ⟨hr,he,hA,ho,Nat.pos_of_ne_zero ha,
        ⟨hl,keys_above_mono rest hl.le hkeys⟩,hs,hse,hB,hBo,hb,hkeys,hrest⟩
    by_cases heq : collectedTagKey rho A=collectedTagKey sigma B
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_pos heq]
      exact ⟨hs,hse,hB,hBo,by omega,hkeys,hrest⟩
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_neg heq]
      exact ⟨hs,hse,hB,hBo,hb,
        insert_keys_above rho A a _ rest (by omega) hkeys,ih hrest⟩

private theorem valid_tags_support (tags : CollectedPositiveTags) (ht : CollectedTagsValid tags) :
    collectedTagsSupport tags=false ↔ tags=.nil := by
  cases tags with
  | nil => simp [collectedTagsSupport]
  | cons rho A a rest =>
    have hA : collectedPositiveSupport A=true := ht.2.2.2.1
    simp [collectedTagsSupport,hA]

private theorem insert_nonempty (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (tags : CollectedPositiveTags) (ha : 0<a) : collectedTagInsert rho A a tags≠.nil := by
  cases tags with
  | nil => simp [collectedTagInsert,Nat.ne_of_gt ha]
  | cons sigma B b rest =>
    simp only [collectedTagInsert,if_neg (Nat.ne_of_gt ha)]
    split <;> try simp
    split <;> simp

private theorem insert_support_true (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (tags : CollectedPositiveTags) (hr : Order.IsSuccLimit rho.1.repr)
    (he : rho.1.repr<epsilonZero) (hA : CollectedPositiveValid A)
    (ho : collectedPositiveSupport A=true) (ha : 0<a) (ht : CollectedTagsValid tags) :
    collectedTagsSupport (collectedTagInsert rho A a tags)=true := by
  have hv := collectedTagInsertValid rho A a tags hr he hA ho ht
  have hn := insert_nonempty rho A a tags ha
  cases hs : collectedTagsSupport (collectedTagInsert rho A a tags) with
  | false => exact False.elim (hn ((valid_tags_support _ hv).mp hs))
  | true => rfl

theorem collectedTagsMergeCorrect : Targets.CollectedTagsMergeCorrect := by
  intro left right hl hr
  induction left using tags_tail_induction with
  | nil =>
    refine ⟨hr,?_,?_⟩
    · simp [collectedTagsMerge,collectedTagsSupport]
    · intro x; simp [collectedTagsMerge,actualCollectedTagsEval]
  | cons rho A a rest ih =>
    rcases hl with ⟨hlim,hbelow,hA,hopen,ha,hkeys,hrest⟩
    have hi := ih hrest
    refine ⟨collectedTagInsertValid rho A a _ hlim hbelow hA hopen hi.1,?_,?_⟩
    · rw [collectedTagsMerge,insert_support_true rho A a _ hlim hbelow hA hopen ha hi.1]
      simp [collectedTagsSupport,hopen]
    · intro x
      rw [collectedTagsMerge,collectedTagInsertValue,hi.2.2 x]
      simp only [actualCollectedTagsEval]
      omega

theorem collectedPositiveAddCorrect : Targets.CollectedPositiveAddCorrect := by
  intro A B hA hB
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      have hm := collectedTagsMergeCorrect tags rest hA hB
      refine ⟨hm.1,?_,?_⟩
      · simp only [collectedPositiveAdd,collectedPositiveSupport,hm.2.1]
        by_cases hb : b=0 <;> by_cases he : e=0 <;>
          simp [hb,he,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm]
        have hb' : (b != 0)=true := bne_iff_ne.mpr hb
        have hs' : (b+e != 0)=true := bne_iff_ne.mpr (by omega)
        rw [hb',hs']
        rfl
      · intro x
        simp only [collectedPositiveAdd,actualCollectedPositiveEval,hm.2.2 x,Nat.add_mul]
        omega

end LogicLineages.OrdinalComparison
