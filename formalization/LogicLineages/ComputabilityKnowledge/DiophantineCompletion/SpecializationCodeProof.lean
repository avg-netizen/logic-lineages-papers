module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationTargets
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationCodeProof
open PolynomialCircuit Specialization SpecializationTargets

private theorem encodeTermsAppend (as bs : Monomials) :
    encodeTerms (as ++ bs) = encodeTerms as ++ encodeTerms bs := by
  induction as with
  | nil => rfl
  | cons m ms ih =>
      rcases m with ⟨z,vs⟩
      cases z <;> simp [encodeTerms,ih,List.append_assoc]

private theorem rawTermCorrect (x : Nat) (m : Monomial) :
    rawTerm x m = encodeTerms [term x m] := by
  rcases m with ⟨z,vs⟩
  cases z with
  | ofNat k =>
      have hc : Int.ofNat k * (x : Int) ^ vs.count 0 = Int.ofNat (k * x ^ vs.count 0) := by
        simp [Int.ofNat_eq_natCast]
      simp only [rawTerm,term]
      rw [hc]
      simp [encodeTerms]
  | negSucc k =>
      let mag := (k + 1) * x ^ vs.count 0
      have hc : Int.negSucc k * (x : Int) ^ vs.count 0 = -(mag : Int) := by
        simp only [mag,Int.negSucc_eq,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
        ring
      by_cases hz : mag = 0
      · have hcoef : Int.negSucc k * (x : Int) ^ vs.count 0 = Int.ofNat 0 := by
          rw [hc,hz]
          rfl
        simp [rawTerm,term,hcoef,show (k + 1) * x ^ vs.count 0 = 0 from hz,encodeTerms]
      · have hcoef : Int.negSucc k * (x : Int) ^ vs.count 0 = Int.negSucc (mag - 1) := by
          rw [hc,Int.negSucc_eq]
          omega
        simp [rawTerm,term,hcoef,show (k + 1) * x ^ vs.count 0 ≠ 0 from hz,encodeTerms,mag]

private theorem rawTermsCorrect (x : Nat) (ms : Monomials) :
    rawTerms x ms = encodeTerms (ms.map (term x)) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
      rw [rawTerms,rawTermCorrect,ih,List.map_cons]
      exact (encodeTermsAppend [term x m] (ms.map (term x))).symm

theorem specializationCodeCalibration : SpecializationCodeCalibration := by
  intro p x
  unfold specializationCode
  rw [rawTermsCorrect]
  rfl

private theorem prCons {f : Nat → Nat} {g : Nat → List Nat}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => f x :: g x) :=
  Primrec.list_cons.comp hf hg

private theorem prPower (k : Nat) : Primrec (fun x : Nat => x ^ k) :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp Primrec.id (Primrec.const k)

private theorem prRawTerm (m : Monomial) : Primrec (fun x : Nat => rawTerm x m) := by
  rcases m with ⟨z,vs⟩
  cases z with
  | ofNat k =>
      exact prCons (Primrec.const 0)
        (prCons (Primrec.nat_mul.comp (Primrec.const k) (prPower (vs.count 0)))
          (Primrec.const ((dropParameter vs).length :: dropParameter vs)))
  | negSucc k =>
      have hmag : Primrec (fun x : Nat => (k + 1) * x ^ vs.count 0) :=
        Primrec.nat_mul.comp (Primrec.const (k + 1)) (prPower (vs.count 0))
      exact Primrec.ite (Primrec.eq.comp hmag (Primrec.const 0))
        (Primrec.const (0 :: 0 :: (dropParameter vs).length :: dropParameter vs))
        (prCons (Primrec.const 1)
          (prCons (Primrec.nat_sub.comp hmag (Primrec.const 1))
            (Primrec.const ((dropParameter vs).length :: dropParameter vs))))

private theorem prRawTerms (ms : Monomials) : Primrec (fun x : Nat => rawTerms x ms) := by
  induction ms with
  | nil => exact Primrec.const []
  | cons m ms ih => exact Primrec.list_append.comp (prRawTerm m) ih

theorem specializationCodePrimrec : SpecializationCodePrimrec := by
  intro p
  exact Primrec.encode.comp (prCons (Primrec.const (p.inputCount - 1)) (prRawTerms p.monomials))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationCodeProof
