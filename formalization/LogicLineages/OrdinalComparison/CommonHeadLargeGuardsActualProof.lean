module
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsMaskProof
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Proof
open CommonHeadLargeRow CommonHeadCollectedRow

private theorem block_eval (cs : List Int) (i : Nat) (desired : Int) (ν : Nat→Nat) :
    (blockFormula cs i desired).eval ν ↔ Int.sign (coefficient (inputRow cs ν) (ν i))=desired :=
  exactBlockFormula cs i desired ν

private theorem input_member (cs : List Int) (ν : Nat→Nat) (a : Int×Nat)
    (ha : a∈inputRow cs ν) : ∃ i<cs.length, ν i=a.2 := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact ⟨b.2,by simpa using List.snd_lt_of_mem_zipIdx hb,rfl⟩
private theorem input_at (cs : List Int) (ν : Nat→Nat) (i : Nat) (hi : i<cs.length) :
    (cs[i],ν i)∈inputRow cs ν := by
  apply List.mem_map.mpr
  refine ⟨(cs[i],i),?_,rfl⟩
  exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
private theorem collected_at (row : Row) (t : Nat) (hkey : ∃ b∈row,b.2=t)
    (hne : coefficient row t≠0) : (coefficient row t,t)∈collect row := by
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr ⟨t,?_,rfl⟩,?_⟩
  · simp only [keys,List.mem_dedup]
    exact List.mem_map.mpr hkey
  · simpa using hne
private theorem threshold_input (K : Int) (cs : List Int) (ν : Nat→Nat) :
    threshold K (inputRow cs ν)=originalThreshold K cs := by
  have h := congrArg (fun xs : List Int=>(xs.map Int.natAbs).sum) (List.zipIdx_map_fst 0 cs)
  simp only [List.map_map,Function.comp_def] at h
  simpa only [threshold,originalThreshold,mass,inputRow,List.map_map,Function.comp_def,h]

private theorem canceled_iff (cs : List Int) (ν : Nat→Nat) :
    (canceledFormula cs).eval ν ↔ collect (inputRow cs ν)=[] := by
  have he : (canceledFormula cs).eval ν ↔
      ∀ i<cs.length, coefficient (inputRow cs ν) (ν i)=0 := by
    simp only [canceledFormula,conjunction_eval,List.mem_map,List.mem_range,forall_exists_index,
      and_imp,forall_apply_eq_imp_iff₂,block_eval,Int.sign_eq_zero_iff_zero]
  rw [he]
  constructor
  · intro hz
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro a ha
    obtain ⟨hn,hcoef,b,hb,hba⟩ := (CommonHeadCollectedRow.Proof.literalCollectedSupport (inputRow cs ν)).2.1 a ha
    obtain ⟨i,hi,heq⟩ := input_member cs ν b hb
    apply hn
    rw [hcoef,← hba,← heq,hz i hi]
  · intro hempty i hi
    by_contra hn
    have hm := collected_at (inputRow cs ν) (ν i) ⟨(cs[i],ν i),input_at cs ν i hi,rfl⟩ hn
    rw [hempty] at hm
    exact List.not_mem_nil hm

private theorem maximal_eval (cs : List Int) (i : Nat) (ν : Nat→Nat) :
    (maximalFormula cs i).eval ν ↔
      ∀ j<cs.length, ¬ν i<ν j ∨ coefficient (inputRow cs ν) (ν j)=0 := by
  simp only [maximalFormula,conjunction_eval,List.mem_map,List.mem_range,forall_exists_index,
    and_imp,forall_apply_eq_imp_iff₂,Formula.eval,block_eval,Int.sign_eq_zero_iff_zero]

private theorem sign_eval (K : Int) (cs : List Int) (desired : Int) (ν : Nat→Nat) :
    (signFormula K cs desired).eval ν ↔
      (Int.sign K=desired ∧ collect (inputRow cs ν)=[]) ∨
      (desired≠0 ∧ ∃ i<cs.length,
        Int.sign (coefficient (inputRow cs ν) (ν i))=desired ∧ (maximalFormula cs i).eval ν) := by
  have htruth (P : Prop) [Decidable P] : (if P then Formula.truth else Formula.falsity).eval ν ↔ P := by
    by_cases h : P <;> simp [h,Formula.eval]
  simp only [signFormula,Formula.eval,htruth,canceled_iff]
  by_cases hd : desired=0
  · simp only [if_true,Formula.eval,hd,ne_eq,not_true_eq_false,false_and,or_false]
  · simp [hd,disjunction_eval,Formula.eval,block_eval]

private theorem actual_sign (lam : Ordinal) (hl : lam<epsilonZero) (hs : Order.IsSuccLimit lam)
    (K : Int) (cs : List Int) (desired : Int) (ν : Nat→Nat)
    (hdom : ∀ i<cs.length,actualOrdinalNorm lam≤ν i)
    (hlarge : ∀ i<cs.length,originalThreshold K cs≤ν i) :
    (signFormula K cs desired).eval ν ↔ Int.sign (value lam K (inputRow cs ν))=desired := by
  have hrow : ∀ a∈inputRow cs ν,actualOrdinalNorm lam≤a.2 ∧ threshold K (inputRow cs ν)≤a.2 := by
    intro a ha
    obtain ⟨i,hi,he⟩ := input_member cs ν a ha
    rw [← he,threshold_input]
    exact ⟨hdom i hi,hlarge i hi⟩
  have hactual := CommonHeadCollectedRow.Proof.actualCollectedDominance lam hl hs K (inputRow cs ν) hrow
  have hsupport := CommonHeadCollectedRow.Proof.literalCollectedSupport (inputRow cs ν)
  rw [sign_eval]
  constructor
  · rintro (⟨hk,hempty⟩ | ⟨hd,i,hi,hcoef,hmax⟩)
    · rw [hactual.1 hempty]
      exact hk
    · have hn : coefficient (inputRow cs ν) (ν i)≠0 := by
        intro hz
        apply hd
        rw [← hcoef,hz,Int.sign_zero]
      have ha := collected_at (inputRow cs ν) (ν i) ⟨(cs[i],ν i),input_at cs ν i hi,rfl⟩ hn
      have hgreat : ∀ b∈collect (inputRow cs ν),b.2≤ν i := by
        intro b hb
        by_contra hnot
        have hlt : ν i<b.2 := lt_of_not_ge hnot
        obtain ⟨hbnon,hbcoef,c,hc,hcb⟩ := hsupport.2.1 b hb
        obtain ⟨j,hj,hej⟩ := input_member cs ν c hc
        have he : ν j=b.2 := hej.trans hcb
        rcases (maximal_eval cs i ν).mp hmax j hj with h | h
        · exact h (by simpa only [he] using hlt)
        · apply hbnon
          rw [hbcoef,← he,h]
      exact (hactual.2.2 _ ha hgreat).trans hcoef
  · intro hsign
    by_cases hempty : collect (inputRow cs ν)=[]
    · left
      exact ⟨by rwa [hactual.1 hempty] at hsign,hempty⟩
    · obtain ⟨a,ha,hmax,hsgn⟩ := hactual.2.1 hempty
      obtain ⟨hn,hcoef,b,hb,hba⟩ := hsupport.2.1 a ha
      obtain ⟨i,hi,hei⟩ := input_member cs ν b hb
      have he : ν i=a.2 := hei.trans hba
      have hd : desired≠0 := by
        intro hz
        apply hn
        apply Int.eq_zero_of_sign_eq_zero
        exact hsgn.symm.trans (hsign.trans hz)
      refine Or.inr ⟨hd,i,hi,?_,?_⟩
      · rw [he,← hcoef]
        exact hsgn.symm.trans hsign
      · apply (maximal_eval cs i ν).mpr
        intro j hj
        by_cases hlt : ν i<ν j
        · right
          by_contra hnon
          have hm := collected_at (inputRow cs ν) (ν j) ⟨(cs[j],ν j),input_at cs ν j hj,rfl⟩ hnon
          have hh := hmax _ hm
          rw [← he] at hh
          exact (not_le_of_gt hlt) hh
        · exact Or.inl hlt

theorem exactActualLargeFormula : Targets.ExactActualLargeFormula := by
  intro lam hl hs K cs desired ν hdom
  have hb : (conjunction ((List.range cs.length).map (Formula.bound (originalThreshold K cs)))).eval ν ↔
      ∀ i<cs.length,originalThreshold K cs≤ν i := by
    simp only [conjunction_eval,List.mem_map,List.mem_range,forall_exists_index,and_imp,
      forall_apply_eq_imp_iff₂,Formula.eval]
  change (_ ∧ (signFormula K cs desired).eval ν) ↔ _
  rw [hb]
  constructor
  · rintro ⟨hlarge,hf⟩
    exact ⟨hlarge,(actual_sign lam hl hs K cs desired ν hdom hlarge).mp hf⟩
  · rintro ⟨hlarge,hf⟩
    exact ⟨hlarge,(actual_sign lam hl hs K cs desired ν hdom hlarge).mpr hf⟩
end LogicLineages.OrdinalComparison.CommonHeadLargeGuards.Proof
