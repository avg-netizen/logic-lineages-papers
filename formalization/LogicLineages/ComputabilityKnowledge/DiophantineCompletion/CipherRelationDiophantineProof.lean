module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationArithmeticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesDiophantineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDiophantineProof
open Dioph Cipher CipherRelation CipherRelationTargets

private theorem onesReindexed {α : Type} (n q : α) :
    Dioph {v : Option (Option α) → Nat |
      v (some (some n))+1<v (some (some q)) ∧
      v (some none)=ones (v (some (some n))) (v (some (some q))) ∧
      v none=shiftedOnes (v (some (some n))) (v (some (some q)))} := by
  let f : Fin 4 → Option (Option α) := fun i =>
    if i=0 then some (some n) else if i=1 then some (some q) else if i=2 then some none else none
  simpa [f,Function.comp_def] using
    Dioph.reindex_dioph (Option (Option α)) f CipherOnesDiophantineProof.onesDiophantine

theorem codeDiophantine : CodeDiophantine := by
  let α := Option (Option (Fin 3))
  have ho := onesReindexed (0 : Fin 3) 1
  have hq : DiophFn (fun v : α → Nat => v (some (some 1))) := Dioph.proj_dioph _
  have ha : DiophFn (fun v : α → Nat => v (some (some 2))) := Dioph.proj_dioph _
  have hu : DiophFn (fun v : α → Nat => v (some none)) := Dioph.proj_dioph _
  have hm := Dioph.mul_dioph
    (Dioph.sub_dioph (Dioph.pow_dioph (Dioph.const_dioph 2) hq) (Dioph.const_dioph 1)) hu
  have he := Dioph.eq_dioph (MaskingProof.bitAndDiophantine _ _ _ ha hm) ha
  have h := Dioph.ex1_dioph (Dioph.ex1_dioph (ho.inter he))
  apply h.ext
  intro v
  change (∃ u u1 : Nat, (v 0+1<v 1 ∧ u=ones (v 0) (v 1) ∧ u1=shiftedOnes (v 0) (v 1)) ∧
      (v 2 &&& ((2^(v 1)-1)*u))=v 2) ↔ Code (v 0) (v 1) (v 2)
  rw [show Code (v 0) (v 1) (v 2) ↔ v 0+1<v 1 ∧
    (v 2 &&& ((2^(v 1)-1)*ones (v 0) (v 1)))=v 2 from
      CipherValidityProof.cipherValidityCharacterization (v 0) (v 1) (v 2)]
  constructor
  · rintro ⟨u,u1,⟨hq,rfl,rfl⟩,he⟩
    exact ⟨hq,he⟩
  · rintro ⟨hq,he⟩
    exact ⟨ones (v 0) (v 1),shiftedOnes (v 0) (v 1),⟨hq,rfl,rfl⟩,he⟩

theorem constDiophantine : ConstDiophantine := by
  let α := Option (Option (Fin 4))
  have ho := onesReindexed (0 : Fin 4) 1
  have hn : DiophFn (fun v : α → Nat => v (some (some 0))) := Dioph.proj_dioph _
  have hq : DiophFn (fun v : α → Nat => v (some (some 1))) := Dioph.proj_dioph _
  have hc : DiophFn (fun v : α → Nat => v (some (some 2))) := Dioph.proj_dioph _
  have ha : DiophFn (fun v : α → Nat => v (some (some 3))) := Dioph.proj_dioph _
  have hu : DiophFn (fun v : α → Nat => v (some none)) := Dioph.proj_dioph _
  have hb := (Dioph.eq_dioph hn (Dioph.const_dioph 0)).union
    (Dioph.lt_dioph hc (Dioph.pow_dioph (Dioph.const_dioph 2) hq))
  have he := Dioph.eq_dioph ha (Dioph.mul_dioph hc hu)
  have h := Dioph.ex1_dioph (Dioph.ex1_dioph (ho.inter (hb.inter he)))
  apply h.ext
  intro v
  change (∃ u u1 : Nat, (v 0+1<v 1 ∧ u=ones (v 0) (v 1) ∧ u1=shiftedOnes (v 0) (v 1)) ∧
    (v 0=0 ∨ v 2<2^(v 1)) ∧ v 3=v 2*u) ↔ Const (v 0) (v 1) (v 2) (v 3)
  rw [CipherRelationArithmeticProof.constantArithmeticCharacterization]
  constructor
  · rintro ⟨u,u1,⟨hq,rfl,rfl⟩,hb,he⟩
    exact ⟨hq,hb,he⟩
  · rintro ⟨hq,hb,he⟩
    exact ⟨ones (v 0) (v 1),shiftedOnes (v 0) (v 1),⟨hq,rfl,rfl⟩,hb,he⟩

theorem addDiophantine : AddDiophantine :=
  Dioph.eq_dioph (Dioph.proj_dioph (0 : Fin 3))
    (Dioph.add_dioph (Dioph.proj_dioph 1) (Dioph.proj_dioph 2))

theorem multDiophantine : MultDiophantine := by
  let α := Option (Option (Fin 5))
  have ho := onesReindexed (0 : Fin 5) 1
  have hq : DiophFn (fun v : α → Nat => v (some (some 1))) := Dioph.proj_dioph _
  have ha : DiophFn (fun v : α → Nat => v (some (some 2))) := Dioph.proj_dioph _
  have hb : DiophFn (fun v : α → Nat => v (some (some 3))) := Dioph.proj_dioph _
  have hc : DiophFn (fun v : α → Nat => v (some (some 4))) := Dioph.proj_dioph _
  have hu : DiophFn (fun v : α → Nat => v (some none)) := Dioph.proj_dioph _
  have hv : DiophFn (fun v : α → Nat => v none) := Dioph.proj_dioph _
  have hr : DiophFn (fun v : α → Nat => base (v (some (some 1)))) :=
    Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.mul_dioph (Dioph.const_dioph 4) hq)
  have hm := Dioph.mul_dioph (Dioph.sub_dioph hr (Dioph.const_dioph 1)) hv
  have he := Dioph.eq_dioph (MaskingProof.bitAndDiophantine _ _ _ (Dioph.mul_dioph ha hu) hm)
    (MaskingProof.bitAndDiophantine _ _ _ (Dioph.mul_dioph hb hc) hm)
  have hex := Dioph.ex1_dioph (Dioph.ex1_dioph (ho.inter he))
  have hmasked : Dioph {v : Fin 5 → Nat | v 0+1<v 1 ∧
      (v 2*ones (v 0) (v 1)) &&& ((base (v 1)-1)*shiftedOnes (v 0) (v 1)) =
      (v 3*v 4) &&& ((base (v 1)-1)*shiftedOnes (v 0) (v 1))} := by
    apply hex.ext
    intro v
    change (∃ u u1 : Nat, (v 0+1<v 1 ∧ u=ones (v 0) (v 1) ∧ u1=shiftedOnes (v 0) (v 1)) ∧
      (v 2*u) &&& ((base (v 1)-1)*u1) = (v 3*v 4) &&& ((base (v 1)-1)*u1)) ↔ _
    constructor
    · rintro ⟨u,u1,⟨hq,rfl,rfl⟩,he⟩
      exact ⟨hq,he⟩
    · rintro ⟨hq,he⟩
      exact ⟨ones (v 0) (v 1),shiftedOnes (v 0) (v 1),⟨hq,rfl,rfl⟩,he⟩
  have hz := Dioph.eq_dioph (Dioph.proj_dioph (0 : Fin 5)) (Dioph.const_dioph 0)
  have hp := Dioph.lt_dioph (Dioph.const_dioph 0) (Dioph.proj_dioph (0 : Fin 5))
  exact (hz.union (hp.inter hmasked)).ext
    (fun v => (CipherRelationArithmeticProof.multiplicationArithmeticCharacterization
      (v 0) (v 1) (v 2) (v 3) (v 4)).symm)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherRelationDiophantineProof
