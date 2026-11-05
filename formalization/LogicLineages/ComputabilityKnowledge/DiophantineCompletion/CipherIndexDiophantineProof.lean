module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexArithmeticProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesDiophantineProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexDiophantineProof
open Dioph Cipher CipherIndex CipherIndexTargets

theorem indexDiophantine : IndexDiophantine := by
  let α := Option (Option (Fin 3))
  let N : (α → Nat) → Nat := fun v => v (some (some 0))
  let Q : (α → Nat) → Nat := fun v => v (some (some 1))
  let A : (α → Nat) → Nat := fun v => v (some (some 2))
  let U : (α → Nat) → Nat := fun v => v (some none)
  let V : (α → Nat) → Nat := fun v => v none
  let map : Fin 4 → α := fun i =>
    if i=0 then some (some 0) else if i=1 then some (some 1) else if i=2 then some none else none
  have ho : Dioph {v : α → Nat | N v+1<Q v ∧ U v=ones (N v) (Q v) ∧ V v=shiftedOnes (N v) (Q v)} := by
    simpa [map, N, Q, U, V, Function.comp_def] using
      Dioph.reindex_dioph α map CipherOnesDiophantineProof.onesDiophantine
  have hn : DiophFn N := Dioph.proj_dioph (some (some 0))
  have hq : DiophFn Q := Dioph.proj_dioph (some (some 1))
  have ha : DiophFn A := Dioph.proj_dioph (some (some 2))
  have hu : DiophFn U := Dioph.proj_dioph (some none)
  have hv : DiophFn V := Dioph.proj_dioph none
  have hb : DiophFn (fun v => base (Q v)) :=
    Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.mul_dioph (Dioph.const_dioph 4) hq)
  have ht : DiophFn (fun v => (base (Q v))^(2^(N v+1))) :=
    Dioph.pow_dioph hb (Dioph.pow_dioph (Dioph.const_dioph 2)
      (Dioph.add_dioph hn (Dioph.const_dioph 1)))
  have hm := Dioph.mul_dioph (Dioph.sub_dioph hb (Dioph.const_dioph 1)) hv
  have hp := MaskingProof.bitAndDiophantine _ _ _ (Dioph.mul_dioph ha hu) hm
  have he := Dioph.eq_dioph (Dioph.add_dioph hp hv) (Dioph.add_dioph ha (Dioph.mul_dioph hn ht))
  have hex := Dioph.ex1_dioph (Dioph.ex1_dioph (ho.inter he))
  apply hex.ext
  intro v
  change (∃ u u1 : Nat,
      (v 0+1<v 1 ∧ u=ones (v 0) (v 1) ∧ u1=shiftedOnes (v 0) (v 1)) ∧
      ((v 2*u) &&& ((base (v 1)-1)*u1))+u1 = v 2+v 0*(base (v 1))^(2^(v 0+1))) ↔
    v 0+1<v 1 ∧ v 2=index (v 0) (v 1)
  constructor
  · rintro ⟨u,u1,⟨hq,rfl,rfl⟩,he⟩
    exact (CipherIndexArithmeticProof.indexArithmeticCharacterization (v 0) (v 1) (v 2)).2 ⟨hq,he⟩
  · intro h
    have he := (CipherIndexArithmeticProof.indexArithmeticCharacterization (v 0) (v 1) (v 2)).1 h
    exact ⟨ones (v 0) (v 1),shiftedOnes (v 0) (v 1),⟨h.1,rfl,rfl⟩,he.2⟩

theorem indexCipherDiophantine : IndexCipherDiophantine :=
  indexDiophantine.ext (fun v => (CipherIndexArithmeticProof.isCipherOfIndex_iff (v 0) (v 1) (v 2)).symm)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherIndexDiophantineProof
