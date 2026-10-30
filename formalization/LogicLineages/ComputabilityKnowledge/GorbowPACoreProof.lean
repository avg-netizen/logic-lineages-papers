module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowPACore
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInductionProof
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPACoreProof
open GorbowSyntax GorbowStandardInstances GorbowPACore

theorem weakeningRealization : Comparators.GorbowPACore.WeakeningRealization := by
  intro n φ I v x
  exact GorbowFormulaSubstitution.substituteFormula_realize φ I (Fin.cases x v)
    (fun i => Term.var i.succ)

theorem logicalSoundness : Comparators.GorbowPACore.LogicalSoundness := by
  intro n w I v
  cases w with
  | k a b => intro ha _; exact ha
  | s a b c => intro h hab ha; exact h ha (hab ha)
  | classicalContraposition a b =>
      intro h hb
      by_contra ha
      exact h ha hb
  | andLeft a b => intro h; exact h.1
  | andRight a b => intro h; exact h.2
  | andIntro a b => intro ha hb; exact ⟨ha,hb⟩
  | orLeft a b => intro ha; exact Or.inl ha
  | orRight a b => intro hb; exact Or.inr hb
  | orElim a b c => intro ha hb hab; exact hab.elim ha hb
  | existsDualForward a =>
      rintro ⟨x,hx⟩ h
      exact h x hx
  | existsDualBackward a =>
      intro h
      classical
      by_contra hn
      apply h
      intro x hx
      exact hn ⟨x,hx⟩
  | reflexive t => rfl
  | equalityReplace a t u =>
      intro htu ha
      apply (GorbowStandardInstancesProof.literalInstantiation n a u I v).mpr
      have h := (GorbowStandardInstancesProof.literalInstantiation n a t I v).mp ha
      change t.realize I v = u.realize I v at htu
      rw [htu] at h
      exact h
  | allInstantiate a t =>
      intro h
      exact (GorbowStandardInstancesProof.literalInstantiation n a t I v).mpr (h (t.realize I v))
  | allDistribute a b => intro h ha x; exact h x (ha x)
  | allVacuous a =>
      intro h x
      exact (weakeningRealization n a I v x).mpr h

theorem arithmeticSoundness : Comparators.GorbowPACore.ArithmeticSoundness := by
  intro n w I v
  cases w with
  | succNotZero t => exact Nat.succ_ne_zero _
  | succInjective t u => exact Nat.succ.inj
  | addZero t => exact Nat.add_zero _
  | addSucc t u => exact Nat.add_succ _ _
  | mulZero t => exact Nat.mul_zero _
  | mulSucc t u => exact Nat.mul_succ _ _
  | induction a => exact GorbowStandardInductionProof.openInductionRealized n a I v

theorem inductionCalibration : Comparators.GorbowPACore.InductionCalibration := by
  intro n φ
  rfl

theorem proofSoundness : Comparators.GorbowPACore.ProofSoundness := by
  intro n φ p
  induction p with
  | logical w => exact logicalSoundness _ w
  | arithmetic w => exact arithmeticSoundness _ w
  | mp p q hp hq => intro I v; exact hp I v (hq I v)
  | generalize p hp => intro I v x; exact hp I (Fin.cases x v)

theorem gorbowPACore : Comparators.GorbowPACore.Target :=
  ⟨weakeningRealization,logicalSoundness,arithmeticSoundness,inductionCalibration,proofSoundness⟩
end LogicLineages.ComputabilityKnowledge.GorbowPACoreProof
