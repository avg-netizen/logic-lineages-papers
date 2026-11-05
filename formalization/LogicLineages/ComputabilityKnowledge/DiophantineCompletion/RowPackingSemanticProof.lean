module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationArithmeticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexArithmeticProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingSemanticProof
open Elementary Cipher RowPacking RowPackingTargets

theorem constantSpecification : ConstantSpecification := by
  intro len q c a f hf
  constructor
  · rintro ⟨g,hg,hgc⟩
    have he : encode len q f=encode len q g := hf.2.2.symm.trans hg.2.2
    have hfg := (CipherArithmeticProof.cipherInjectivity len q f g hf.1 hf.2.1 hg.2.1).1 he
    intro i hi
    exact (hfg i hi).trans (hgc i hi)
  · intro h
    exact ⟨f,hf,h⟩

theorem packedConstraintSpecification : PackedConstraintSpecification := by
  intro n k len q I ν codes rows c hI hrows
  obtain ⟨o,r⟩ := c
  cases r with
  | constant a =>
      exact constantSpecification len q a (codes o) (fun i => rows i o) (hrows o)
  | «variable» b =>
      change codes o=codes b ↔ ∀ i, i<len → rows i o=rows i b
      rw [(hrows o).2.2,(hrows b).2.2]
      exact CipherArithmeticProof.cipherInjectivity len q _ _ hI.1 (hrows o).2.1 (hrows b).2.1
  | «parameter» a =>
      cases a with
      | none =>
          change codes o=I ↔ ∀ i, i<len → rows i o=i
          rw [(hrows o).2.2,hI.2.2]
          exact CipherArithmeticProof.cipherInjectivity len q _ id hI.1 (hrows o).2.1 hI.2.1
      | some a =>
          exact constantSpecification len q (ν a) (codes o) (fun i => rows i o) (hrows o)
  | add b d =>
      exact CipherRelationArithmeticProof.additionSpecification len q (codes o) (codes b) (codes d)
        (fun i => rows i o) (fun i => rows i b) (fun i => rows i d) (hrows o) (hrows b) (hrows d)
  | mul b d =>
      exact CipherRelationArithmeticProof.multiplicationSpecification len q (codes o) (codes b) (codes d)
        (fun i => rows i o) (fun i => rows i b) (fun i => rows i d) (hrows o) (hrows b) (hrows d)

theorem variableRowPacking : VariableRowPacking := by
  intro n k m C len ν
  classical
  constructor
  · intro h
    let W : Fin len → Fin k → Nat := fun i => Classical.choose (h i.val i.isLt)
    have hW (i : Fin len) : ∀ j, (C j).Holds (indexed i.val ν) (W i) :=
      Classical.choose_spec (h i.val i.isLt)
    let M := Finset.univ.sup (fun t : Fin len × Fin k => W t.1 t.2)
    let q := len+M+2
    let rows : Nat → Fin k → Nat := fun i b => if hi : i<len then W ⟨i,hi⟩ b else 0
    let codes : Fin k → Nat := fun b => encode len q (fun i => rows i b)
    let I := CipherIndex.index len q
    have hq : len+1<q := by dsimp [q]; omega
    have hrows (b : Fin k) : IsCipherOf len q (fun i => rows i b) (codes b) := by
      refine ⟨hq,?_,rfl⟩
      intro i hi
      change (if h : i<len then W ⟨i,h⟩ b else 0)<2^q
      rw [dif_pos hi]
      have hv : W ⟨i,hi⟩ b≤M :=
        Finset.le_sup (f := fun t : Fin len × Fin k => W t.1 t.2) (Finset.mem_univ (⟨i,hi⟩,b))
      have hsmall : W ⟨i,hi⟩ b<q := by dsimp [q]; omega
      exact hsmall.trans (Nat.lt_two_pow_self)
    have hI : IsCipherOf len q id I :=
      (CipherIndexArithmeticProof.isCipherOfIndex_iff len q I).2 ⟨hq,rfl⟩
    refine ⟨q,I,codes,hI,fun b => ⟨_,hrows b⟩,?_⟩
    intro j
    apply (packedConstraintSpecification n k len q I ν codes rows (C j) hI hrows).2
    intro i hi
    have he : rows i=W ⟨i,hi⟩ := by funext b; simp [rows,hi]
    rw [he]
    exact hW ⟨i,hi⟩ j
  · rintro ⟨q,I,codes,hI,hcodes,hpacked⟩
    let f : Fin k → Nat → Nat := fun b => Classical.choose (hcodes b)
    have hf (b : Fin k) : IsCipherOf len q (f b) (codes b) := Classical.choose_spec (hcodes b)
    intro i hi
    refine ⟨fun b => f b i,?_⟩
    intro j
    exact ((packedConstraintSpecification n k len q I ν codes (fun i b => f b i)
      (C j) hI hf).1 (hpacked j)) i hi

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.RowPackingSemanticProof
