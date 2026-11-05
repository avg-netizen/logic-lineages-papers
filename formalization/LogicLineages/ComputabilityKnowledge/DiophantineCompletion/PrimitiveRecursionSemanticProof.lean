module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionSemanticProof
open PrimitiveRecursion PrimitiveRecursionTargets Cipher

theorem finiteTraceCipher : FiniteTraceCipher := by
  intro len f
  let M := (Finset.range len).sup f
  let q := len + M + 2
  refine ⟨q,encode len q f,?_,?_,rfl⟩
  · dsimp [q]
    omega
  · intro i hi
    have hm : f i ≤ M := Finset.le_sup (f := f) (Finset.mem_range.mpr hi)
    have hq : f i < q := by dsimp [q]; omega
    exact hq.trans Nat.lt_two_pow_self

theorem ordinaryPrecTraceSpecification : OrdinaryPrecTraceSpecification := by
  intro base step a n
  induction n with
  | zero =>
      intro y
      rw [Nat.Partrec.Code.eval_prec_zero]
      constructor
      · intro hy
        exact ⟨fun _ => y,⟨hy,fun i hi => by omega⟩,rfl⟩
      · rintro ⟨f,⟨hf,_⟩,hy⟩
        simpa only [hy] using hf
  | succ n ih =>
      intro y
      rw [Nat.Partrec.Code.eval_prec_succ]
      change y ∈ ((Nat.Partrec.Code.eval (.prec base step) (Nat.pair a n)).bind
        (fun z => Nat.Partrec.Code.eval step (Nat.pair a (Nat.pair n z)))) ↔ _
      rw [Part.mem_bind_iff]
      constructor
      · rintro ⟨z,hz,hy⟩
        obtain ⟨f,⟨hf,hstep⟩,hfn⟩ := (ih z).1 hz
        let g : Nat → Nat := fun i => if i ≤ n then f i else y
        refine ⟨g,⟨?_,?_⟩,?_⟩
        · simpa [g] using hf
        · intro i hi
          by_cases h : i = n
          · subst i
            simpa [g,hfn] using hy
          · have hin : i < n := by omega
            have hle : i ≤ n := by omega
            have hnext : i + 1 ≤ n := by omega
            simpa only [g,if_pos hle,if_pos hnext] using hstep i hin
        · simp [g]
      · rintro ⟨f,⟨hf,hstep⟩,hy⟩
        refine ⟨f n,(ih (f n)).2 ⟨f,⟨hf,fun i hi => hstep i (by omega)⟩,rfl⟩,?_⟩
        simpa only [hy] using hstep n (Nat.lt_succ_self n)

theorem codedPrecTraceSpecification : CodedPrecTraceSpecification := by
  intro base step a n y
  rw [ordinaryPrecTraceSpecification]
  constructor
  · rintro ⟨f,⟨hf,hstep⟩,hy⟩
    obtain ⟨q,code,hcode⟩ := finiteTraceCipher (n + 1) f
    have hd (i : Nat) (hi : i < n + 1) : digit q code i = f i := by
      unfold digit
      rw [hcode.2.2]
      exact CipherArithmeticProof.cipherDigitExtraction (n + 1) q f hcode.1 hcode.2.1 i hi
    refine ⟨q,code,⟨f,hcode⟩,⟨?_,?_⟩,?_⟩
    · simpa only [hd 0 (by omega)] using hf
    · intro i hi
      simpa only [hd i (by omega),hd (i + 1) (by omega)] using hstep i hi
    · exact (hd n (by omega)).trans hy
  · rintro ⟨q,code,_,ht,hy⟩
    exact ⟨digit q code,ht,hy⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionSemanticProof
