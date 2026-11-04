module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof

open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open ParametricSourceSuccessor

theorem omegaFreeCalibration : Targets.OmegaFreeCalibration := by
  intro ι index t H i env ρ ht hρ
  unfold evaluate OrdinalSyntaxComputableFold.indexedFold
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  let f : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Nat :=
    OrdinalSyntax.termFold index
    (fun k => leaf ((i, env), k)) (fun k a b => branch H ((i, env), k, a, b))
  change (f t : Ordinal) = denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) t
  induction t with
  | var x =>
      have hn : 8 * index x + 3 ≠ 1 := by omega
      have hm : (8 * index x + 3) % 8 = 3 := by omega
      have hd : (8 * index x + 3) / 8 = index x := by omega
      simp [f, OrdinalSyntax.termFold, leaf, hn, hm, hd, denoteWith]
      simpa only [List.getD_eq_getElem?_getD] using hρ x
  | zero => simp [f, OrdinalSyntax.termFold, leaf, denoteWith]
  | one => simp [f, OrdinalSyntax.termFold, leaf, denoteWith]
  | omega => exact False.elim ht
  | add a b iha ihb =>
      change ((f a + f b : Nat) : Ordinal) = ordinalNaturalSum
        (denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) a)
        (denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) b)
      rw [← iha ht.1, ← ihb ht.2]
      exact (naturalSum_finite (f a) (f b)).symm
  | emul a b iha ihb =>
      change ((2 ^ f a * f b : Nat) : Ordinal) = ordinalNaturalProduct
        ((2 : Ordinal) ^ denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) a)
        (denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) b)
      rw [← iha ht.1, ← ihb ht.2]
      have hp : (2 : Ordinal) ^ (f a : Ordinal) = ((2 ^ f a : Nat) : Ordinal) := by
        simpa only [Ordinal.opow_natCast, Nat.cast_ofNat] using
          (Ordinal.natCast_pow 2 (f a)).symm
      rw [hp]
      exact (naturalProduct_finite (2 ^ f a) (f b)).symm
  | collapse a b iha ihb =>
      change (ParametricFinitePairCollapse.value (fun n => H (i, n)) (f a, f b) : Ordinal) =
        denoteWith (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) (.collapse a b)
      exact (ParametricFiniteCollapseArgument.Proof.denotationCalibration ι
        (fun n => H (i, n)) (fun x => (ρ x : Ordinal)) a b (f a) (f b)
        (iha ht.1).symm (ihb ht.2).symm).symm

end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Proof
