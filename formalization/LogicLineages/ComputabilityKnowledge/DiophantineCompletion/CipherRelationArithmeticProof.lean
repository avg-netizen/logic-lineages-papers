module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherProductProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationArithmeticProof
open Cipher CipherRelation CipherRelationTargets
open scoped BigOperators

private theorem constantEncode (n q c : Nat) : encode n q (fun _ => c)=c*ones n q := by
  simp [encode,ones,Finset.mul_sum]

theorem constantArithmeticCharacterization : ConstantArithmeticCharacterization := by
  intro n q c a
  constructor
  · rintro ⟨f,⟨hq,hf,ha⟩,hc⟩
    refine ⟨hq,?_,?_⟩
    · by_cases hn : n=0
      · exact Or.inl hn
      · exact Or.inr (by have h := hf 0 (by omega); rw [hc 0 (by omega)] at h; exact h)
    · rw [ha, ← constantEncode]
      unfold encode
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc i (Finset.mem_range.mp hi)]
  · rintro ⟨hq,hc,ha⟩
    refine ⟨(fun _ => c),⟨hq,?_,?_⟩,fun _ _ => rfl⟩
    · intro i hi
      rcases hc with hn | hc
      · omega
      · exact hc
    · exact ha.trans (constantEncode n q c).symm

theorem multiplicationArithmeticCharacterization : MultiplicationArithmeticCharacterization := by
  intro n q a b c
  constructor
  · rintro (hn | ⟨hn,u,u1,r',r'',p,hr,hr',⟨hq,hu,hu1⟩,hp,hp'⟩)
    · exact Or.inl hn
    · refine Or.inr ⟨by omega,hq,?_⟩
      have he : r'=base q-1 := by omega
      simp only [hu,hu1,he] at hp hp'
      exact hp.symm.trans hp'
  · rintro (hn | ⟨hn,hq,he⟩)
    · exact Or.inl hn
    · have hb : 1≤base q := Nat.one_le_pow _ _ (by decide)
      refine Or.inr ⟨by omega,ones n q,shiftedOnes n q,base q-1,base q,
        (a*ones n q) &&& ((base q-1)*shiftedOnes n q),rfl,?_,⟨hq,rfl,rfl⟩,rfl,he⟩
      omega

theorem additionSpecification : AdditionSpecification := by
  intro n q a b c f g h hf hg hh
  obtain ⟨hq,hf,ha⟩ := hf
  obtain ⟨_,hg,hb⟩ := hg
  obtain ⟨_,hh,hc⟩ := hh
  change a=b+c ↔ _
  rw [ha,hb,hc]
  exact CipherArithmeticProof.cipherAddition n q f g h hq hf hg hh

theorem multiplicationSpecification : MultiplicationSpecification := by
  intro n q a b c f g h hf hg hh
  obtain ⟨hq,hf,ha⟩ := hf
  obtain ⟨_,hg,hb⟩ := hg
  obtain ⟨_,hh,hc⟩ := hh
  rw [multiplicationArithmeticCharacterization]
  by_cases hn : n=0
  · simp [MultEquations,hn]
  · have hn0 : 0<n := by omega
    simp only [MultEquations,hn,hn0,hq,false_or,true_and]
    rw [ha,hb,hc]
    exact CipherProductProof.cipherMultiplication n q f g h hq hf hg hh

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationArithmeticProof
