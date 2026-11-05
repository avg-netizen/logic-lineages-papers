module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesDiophantineProof
open Dioph Cipher CipherTargets

private theorem equationsBodyDiophantine {α : Type}
    (n q u u1 w u2 : (α → Nat) → Nat)
    (hn : DiophFn n) (hq : DiophFn q) (hu : DiophFn u) (hu1 : DiophFn u1)
    (hw : DiophFn w) (hu2 : DiophFn u2) :
    Dioph {v : α → Nat |
      1+(base (q v)-1)*w v = base (q v)*(base (q v))^(2^(n v+1)) ∧
      u v*u v = u1 v+u2 v ∧
      u1 v = (u v*u v) &&& w v ∧
      u2 v = (u v*u v) &&& (2*w v) ∧
      (base (q v))^2+u1 v = u v+(base (q v))^(2^(n v+1)) ∧
      (base (q v))^4 ∣ u1 v} := by
  have hb : DiophFn (fun v => base (q v)) :=
    Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.mul_dioph (Dioph.const_dioph 4) hq)
  have ht : DiophFn (fun v => (base (q v))^(2^(n v+1))) :=
    Dioph.pow_dioph hb (Dioph.pow_dioph (Dioph.const_dioph 2)
      (Dioph.add_dioph hn (Dioph.const_dioph 1)))
  have hs := Dioph.mul_dioph hu hu
  have h1 := Dioph.eq_dioph
    (Dioph.add_dioph (Dioph.const_dioph 1) (Dioph.mul_dioph
      (Dioph.sub_dioph hb (Dioph.const_dioph 1)) hw)) (Dioph.mul_dioph hb ht)
  have h2 := Dioph.eq_dioph hs (Dioph.add_dioph hu1 hu2)
  have h3 := Dioph.eq_dioph hu1 (MaskingProof.bitAndDiophantine _ _ _ hs hw)
  have h4 := Dioph.eq_dioph hu2 (MaskingProof.bitAndDiophantine _ _ _ hs
    (Dioph.mul_dioph (Dioph.const_dioph 2) hw))
  have h5 := Dioph.eq_dioph (Dioph.add_dioph (Dioph.pow_dioph hb (Dioph.const_dioph 2)) hu1)
    (Dioph.add_dioph hu ht)
  have h6 := Dioph.dvd_dioph (Dioph.pow_dioph hb (Dioph.const_dioph 4)) hu1
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))

private theorem onesEquationsDiophantine {α : Type}
    (n q u u1 : (α → Nat) → Nat)
    (hn : DiophFn n) (hq : DiophFn q) (hu : DiophFn u) (hu1 : DiophFn u1) :
    Dioph {v : α → Nat | OnesEquations (n v) (q v) (u v) (u1 v)} := by
  let lift (f : (α → Nat) → Nat) :=
    fun v : Option (Option α) → Nat => f (fun a => v (some (some a)))
  have hlift (f : (α → Nat) → Nat) (hf : DiophFn f) : DiophFn (lift f) :=
    Dioph.reindex_diophFn (fun a => some (some a)) hf
  have hb := equationsBodyDiophantine (lift n) (lift q) (lift u) (lift u1)
    (fun v => v (some none)) (fun v => v none)
    (hlift n hn) (hlift q hq) (hlift u hu) (hlift u1 hu1)
    (Dioph.proj_dioph (some none)) (Dioph.proj_dioph none)
  have he : Dioph {v : α → Nat | ∃ w u2 : Nat,
      1+(base (q v)-1)*w = base (q v)*(base (q v))^(2^(n v+1)) ∧
      u v*u v = u1 v+u2 ∧
      u1 v = (u v*u v) &&& w ∧
      u2 = (u v*u v) &&& (2*w) ∧
      (base (q v))^2+u1 v = u v+(base (q v))^(2^(n v+1)) ∧
      (base (q v))^4 ∣ u1 v} := Dioph.ex1_dioph (Dioph.ex1_dioph hb)
  have hz := (Dioph.eq_dioph hn (Dioph.const_dioph 0)).inter
    ((Dioph.eq_dioph hu (Dioph.const_dioph 0)).inter
      (Dioph.eq_dioph hu1 (Dioph.const_dioph 0)))
  have hp := (Dioph.lt_dioph (Dioph.const_dioph 0) hn).inter he
  have hd := Dioph.lt_dioph (Dioph.add_dioph hn (Dioph.const_dioph 1)) hq
  exact hd.inter (hz.union hp)

theorem onesDiophantine : OnesDiophantine := by
  have h := onesEquationsDiophantine (fun v : Fin 4 → Nat => v 0) (fun v => v 1)
    (fun v => v 2) (fun v => v 3) (Dioph.proj_dioph 0) (Dioph.proj_dioph 1)
    (Dioph.proj_dioph 2) (Dioph.proj_dioph 3)
  exact h.ext (fun v => (CipherOnesProof.onesArithmeticCharacterization (v 0) (v 1) (v 2) (v 3)).symm)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesDiophantineProof
