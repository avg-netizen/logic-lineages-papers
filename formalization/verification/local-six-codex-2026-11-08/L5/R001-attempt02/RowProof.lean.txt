module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.RowTargets
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.SemanticProof
public import LogicLineages.OrdinalComparison.CounterWordGuardCompletion.LeaderProof
public import LogicLineages.OrdinalComparison.CounterLeaderExpansionProof
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion OuterShiftNormalization
open CounterWordGuardCompletion KernelSourceCompletion

private theorem normalized_sum (as : List (Int × (Nat × Word))) (ν : Nat → Nat)
    (hd : ∀ a ∈ as, WordDomain a.2.2 (ν a.2.1)) :
    (as.map (fun a => a.1*(wordValue a.2.2 (ν a.2.1) : Int))).sum =
      (as.map (fun a => a.1*(wordValue (coreWord a.2.2) (ν a.2.1) : Int))).sum +
      (as.map (fun a => a.1*outerShift a.2.2)).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have hv := OuterShiftNormalization.Proof.normalizationCorrect a.2.2 (ν a.2.1)
        (hd a List.mem_cons_self)
      have hs := ih (fun b hb => hd b (List.mem_cons_of_mem a hb))
      simp only [List.map_cons,List.sum_cons]
      rw [hv.2.2.2,hs]
      ring

theorem exactRowNormalization : Targets.ExactRowNormalization := by
  intro D r ν ha hd
  refine ⟨?_,?_,?_,?_⟩
  · intro a hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    exact (OuterShiftNormalization.Proof.normalizationSyntax D b.2.2 (ha b hb)).1
  · intro a hm
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hm
    exact (OuterShiftNormalization.Proof.normalizationCorrect b.2.2 (ν b.2.1) (hd b hb)).1
  · have hs := normalized_sum r.2 ν hd
    simp only [RowValue,normalizeRow,List.map_map,Function.comp_def]
    rw [hs]
    ring
  · simp only [rowVariables,normalizeRow,List.map_map,Function.comp_def]

private theorem residualWords_length (n c : Nat) :
    (residualWords n c).length = n+1 := by
  induction n with
  | zero => simp [residualWords]
  | succ n ih => simp [residualWords,ih]

private theorem residualWords_allowed (D n c : Nat) : n+3 ≤ D →
    ∀ p ∈ residualWords n c,
      3 ≤ p.1 ∧ p.1 ≤ n+3 ∧ WordAllowed D p.2 := by
  induction n with
  | zero =>
      intro hD p hp
      simp only [residualWords,List.mem_singleton] at hp
      subst p
      refine ⟨by omega,by omega,?_⟩
      intro a ha
      simp only [List.mem_singleton] at ha
      subst a
      simp [LetterAllowed,counterLetter,hD]
  | succ n ih =>
      intro hD p hp
      simp only [residualWords,List.mem_cons,List.mem_map] at hp
      rcases hp with rfl | ⟨q,hq,rfl⟩
      · refine ⟨by omega,by omega,?_⟩
        intro a ha
        simp only [List.mem_singleton] at ha
        subst a
        simp [LetterAllowed,counterLetter]
        omega
      · have hq' := ih (by omega) q hq
        refine ⟨hq'.1,by omega,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [LetterAllowed,kernelLetter]
          omega
        · exact hq'.2.2 a ha

theorem residualWordSyntax : Targets.ResidualWordSyntax := by
  intro D n c hD
  exact ⟨residualWords_length n c,residualWords_allowed D n c hD⟩

private theorem source_count (d c t : Nat) (hd : 1 ≤ d) (ht : c+d+1 ≤ t) :
    sourceCount d c t = CounterLeaderExpansion.count d c t := by
  exact (UniformCompletion.Focused.sourceProcessBridge d c t hd ht).1

theorem residualWordValues : Targets.ResidualWordValues := by
  intro n c t ht
  induction n generalizing t with
  | zero =>
      have hc := source_count 3 (c+3) t (by omega) (by
        unfold leaderTail at ht
        omega)
      simpa [residualWords,wordValue,letterValue,counterLetter,
        CounterLeaderExpansion.residuals,CounterLeaderExpansion.entries] using hc
  | succ n ih =>
      let u := CounterLeaderExpansion.kernel (n+4) (c+n+4) t
      have hb : c+n+4+(n+4)+1 ≤ t := by
        unfold leaderTail at ht
        omega
      have hk := CounterWordGuardCompletion.Proof.source_zero_kernel
        (n+4) (c+n+4) t (by omega) hb
      have hc := source_count (n+4) (c+n+4) t (by omega) hb
      have hu : t ≤ u := CounterLeaderExpansion.Proof.kernel_ge _ _ _
      have hn : leaderTail n c ≤ u :=
        (CounterWordGuardCompletion.Proof.leaderTail_step n c).trans (ht.trans hu)
      have hi := ih u hn
      simp only [residualWords,List.map_cons,List.map_map,Function.comp_def,
        List.sum_cons,wordValue]
      simp only [letterValue,kernelLetter,counterLetter,if_false,show ¬(3:Nat)=0 by decide,
        show ¬(3:Nat)=1 by decide,show ¬(3:Nat)=2 by decide,
        show ¬(4:Nat)=0 by decide,show ¬(4:Nat)=1 by decide,
        show ¬(4:Nat)=2 by decide,show ¬(4:Nat)=3 by decide,if_true]
      rw [hk,hc]
      change CounterLeaderExpansion.count (n+4) (c+n+4) t +
        ((residualWords n c).map (fun p => wordValue p.2 u)).sum = _
      rw [hi]
      simp [CounterLeaderExpansion.residuals,CounterLeaderExpansion.entries,u,Nat.add_assoc]

private theorem member_le_max (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    a ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact Nat.le_max_left _ _
      · exact (ih ha).trans (Nat.le_max_right _ _)

private theorem allowed_append (D : Nat) (A B : Word)
    (hA : WordAllowed D A) (hB : WordAllowed D B) : WordAllowed D (A++B) := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hA a ha
  · exact hB a ha

private theorem sum_scaled_nat (a : Int) (xs : List Nat) :
    (xs.map (fun (n : Nat) => a*(n : Int))).sum = a*(xs.sum : Int) := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add,ih]
      ring

theorem exactSourceCounterExpansion : Targets.ExactSourceCounterExpansion := by
  intro D a i A n c hD hA ν ht
  have hres := (residualWordSyntax D n c hD).2
  have hcounter : WordAllowed D (counterWord A n c) := by
    apply allowed_append D A _ hA
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    simp [LetterAllowed,counterLetter,hD]
  have hleader : WordAllowed D (leaderValueWord A n c) := by
    apply allowed_append D _ _ (allowed_append D A _ hA
      (CounterWordGuardCompletion.Proof.leaderWord_allowed D n c hD))
    intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    simp [LetterAllowed,phiLetter]
  have hresA : ∀ p ∈ residualWords n c, WordAllowed D (A++p.2) := by
    intro p hp
    exact allowed_append D A p.2 hA (hres p hp).2.2
  have htail : ∀ w ∈ expansionWords A n c, wordTail w ≤ ν i := by
    intro w hw
    have hm := member_le_max ((expansionWords A n c).map wordTail) (wordTail w)
      (List.mem_map.mpr ⟨w,hw,rfl⟩)
    exact hm.trans ((Nat.le_max_right _ _).trans ht)
  have hdom : ∀ w ∈ expansionWords A n c, WordAllowed D w → WordDomain w (ν i) := by
    intro w hw ha
    exact (WordGuardCompletion.Proof.wordTailCorrect D w (ν i) ha (htail w hw)).1
  have hsource := hdom _ (by simp [expansionWords]) hcounter
  have hrowAllowed : RowAllowed D (counterExpansionRow a i A n c) := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hleader
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
      exact hresA p hp
  have hrowDomain : RowDomain (counterExpansionRow a i A n c) ν := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hdom _ (by simp [expansionWords]) hleader
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
      have hm : A++p.2 ∈ expansionWords A n c :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨p,hp,rfl⟩))
      exact hdom _ hm (hresA p hp)
  refine ⟨hrowAllowed,hsource,hrowDomain,?_,?_⟩
  · let t := wordValue A (ν i)
    have hr := WordGuardCompletion.Proof.wordReachCorrect D A (leaderTail n c)
      (ν i) hA ((Nat.le_max_left _ _).trans ht)
    have hlt : leaderTail n c ≤ t := hr.2
    have hct := source_count (n+3) c t (by omega) (by
      unfold leaderTail at hlt
      omega)
    have hval : wordValue (counterWord A n c) (ν i) =
        CounterLeaderExpansion.count (n+3) c t := by
      simpa [counterWord,WordAlgebraProof.wordValue_append,wordValue,
        letterValue,counterLetter,t] using hct
    have hlval : wordValue (leaderValueWord A n c) (ν i) =
        CounterLeaderExpansion.leader n c t := by
      simp only [leaderValueWord,WordAlgebraProof.wordValue_append,wordValue,
        letterValue,phiLetter,if_true]
      rw [CounterWordGuardCompletion.Proof.leaderWord_value n c t hlt]
      rfl
    have hs := sum_scaled_nat (2*a)
      ((residualWords n c).map (fun p => wordValue p.2 t))
    simp only [List.map_map,Function.comp_def] at hs
    rw [residualWordValues n c t hlt] at hs
    have he := CounterLeaderExpansion.Proof.exactCounterLeaderIdentity n c t (by
      unfold leaderTail at hlt
      unfold CounterLeaderExpansion.threshold
      omega)
    have hhalf : (CounterLeaderExpansion.leader n c t : Int) =
        2*((CounterLeaderExpansion.leader n c t / 2 : Nat) : Int) := by
      rcases he.1 with ⟨k,hk⟩
      omega
    simp only [RowValue,counterExpansionRow,List.map_cons,List.map_map,
      Function.comp_def,List.sum_cons]
    rw [hval,hlval]
    simp only [WordAlgebraProof.wordValue_append]
    change 2*a*(CounterLeaderExpansion.count (n+3) c t : Int) =
      2*a*(1-(((c+1)/2 : Nat) : Int)) +
        (a*(CounterLeaderExpansion.leader n c t : Int) +
          ((residualWords n c).map (fun p => 2*a*(wordValue p.2 t : Int))).sum)
    rw [hs,he.2.2,hhalf]
    ring
  · intro j hj
    simp only [rowVariables,counterExpansionRow,List.map_cons,List.map_map,
      Function.comp_def,List.mem_cons,List.mem_map] at hj
    rcases hj with rfl | ⟨p,_,rfl⟩ <;> rfl

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.Proof
