module
public import LogicLineages.OrdinalComparison.FiniteTailTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace LogicLineages.OrdinalComparison

open Vendor.R1

/-- Append a finite ordinal, collecting an existing exponent-zero block. -/
def rawFiniteTail : ONote → Nat → ONote
  | .zero, n => ONote.ofNat n
  | .oadd .zero c _, n => .oadd .zero ⟨(c : Nat) + n, by have := c.pos; omega⟩ .zero
  | .oadd e@(.oadd _ _ _) c t, n => .oadd e c (rawFiniteTail t n)

theorem rawFiniteTail_repr (a : ONote) (ha : ONote.NF a) (n : Nat) :
    (rawFiniteTail a n).repr = a.repr + (n : Ordinal) := by
  induction a with
  | zero => simp only [rawFiniteTail, ONote.repr_ofNat, ONote.repr, zero_add]
  | oadd e c t ihe iht =>
      cases e with
      | zero =>
          have ht : t = 0 := ha.zero_of_zero rfl
          subst t
          simp [rawFiniteTail, ONote.repr, Nat.cast_add]
      | oadd e' c' t' =>
          simp only [rawFiniteTail, ONote.repr, iht ha.snd, add_assoc]

theorem rawFiniteTail_norm (a : ONote) (ha : ONote.NF a) (n : Nat) :
    treeWeight (rawFiniteTail a n) = treeWeight a + n := by
  induction a with
  | zero =>
      cases n <;> simp [rawFiniteTail, ONote.ofNat, treeWeight]
  | oadd e c t ihe iht =>
      cases e with
      | zero =>
          have ht : t = 0 := ha.zero_of_zero rfl
          subst t
          simp only [rawFiniteTail, treeWeight, Nat.add_zero, Nat.mul_one]
          rfl
      | oadd e' c' t' =>
          simp only [rawFiniteTail, treeWeight, iht ha.snd, Nat.add_assoc]

theorem rawFiniteTail_normal (a : ONote) (ha : ONote.NF a) (n : Nat) :
    ONote.NF (rawFiniteTail a n) := by
  induction a with
  | zero => exact ONote.nf_ofNat n
  | oadd e c t ihe iht =>
      cases e with
      | zero => exact ONote.NF.oadd ONote.NF.zero _ ONote.NFBelow.zero
      | oadd e' c' t' =>
          have hne : (ONote.oadd e' c' t').repr ≠ 0 :=
            (show 0 < (ONote.oadd e' c' t').repr from ONote.oadd_pos _ _ _).ne'
          have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hne
          have ht : (rawFiniteTail t n).repr <
              Ordinal.omega0 ^ (ONote.oadd e' c' t').repr := by
            rw [rawFiniteTail_repr t ha.snd n]
            exact hlim.add_natCast_lt ha.snd'.repr_lt n
          exact ONote.NF.oadd ha.fst _ (ONote.NF.below_of_lt' ht (iht ha.snd))

def finiteTail (a : NONote) (n : Nat) : NONote :=
  ⟨rawFiniteTail a.1 n, rawFiniteTail_normal a.1 a.2 n⟩

theorem finiteTailCorrect : Targets.FiniteTailCorrect finiteTail :=
  fun a n => ⟨rawFiniteTail_repr a.1 a.2 n, rawFiniteTail_norm a.1 a.2 n⟩

end LogicLineages.OrdinalComparison
