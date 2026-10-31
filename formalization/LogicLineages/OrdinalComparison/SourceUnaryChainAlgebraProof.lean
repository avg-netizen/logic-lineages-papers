module
public import LogicLineages.OrdinalComparison.SourceUnaryChainTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
public import Mathlib.SetTheory.Ordinal.Principal
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem coeff_finite (a e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 a e < Ordinal.omega0 := by
  by_cases he : e ∈ (Ordinal.CNF Ordinal.omega0 a).map Prod.fst
  · obtain ⟨⟨e,c⟩, hm, rfl⟩ := List.mem_map.mp he
    rw [Ordinal.CNF.coeff_of_mem_CNF hm]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hm
  · rw [Ordinal.CNF.coeff_of_notMem_CNF he]
    exact Ordinal.omega0_pos

private theorem sum_coeff (a b : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum a b) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b := by
  apply Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
  intro e
  exact Ordinal.isPrincipal_add_omega0 (coeff_finite a e) (coeff_finite b e)

theorem sum_assoc (a b c : Ordinal) :
    ordinalNaturalSum (ordinalNaturalSum a b) c =
      ordinalNaturalSum a (ordinalNaturalSum b c) := by
  change Ordinal.CNF.eval Ordinal.omega0
    (Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum a b) + Ordinal.CNF.coeff Ordinal.omega0 c) =
    Ordinal.CNF.eval Ordinal.omega0
    (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum b c))
  rw [sum_coeff, sum_coeff, add_assoc]

theorem sum_comm (a b : Ordinal) : ordinalNaturalSum a b = ordinalNaturalSum b a := by
  unfold ordinalNaturalSum
  apply congrArg (Ordinal.CNF.eval Ordinal.omega0)
  ext e
  simp only [Finsupp.add_apply]
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (coeff_finite a e)
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (coeff_finite b e)
  rw [hm, hn, ← Nat.cast_add, ← Nat.cast_add, Nat.add_comm]

theorem head_step (a b : Ordinal) :
    ordinalNaturalSum (ordinalNaturalSum a 1)
      (ordinalNaturalSum (ordinalNaturalSum 1 b) 1) =
    ordinalNaturalSum (ordinalNaturalSum a 3) b := by
  have h11 : ordinalNaturalSum 1 1 = (2 : Ordinal) := by
    simpa using naturalSum_finite 1 1
  have h3 : ordinalNaturalSum 1 (ordinalNaturalSum 1 1) = (3 : Ordinal) := by
    rw [h11]
    simpa using naturalSum_finite 1 2
  rw [sum_assoc a 1 _, sum_assoc 1 b 1, sum_comm b 1, ← h3]
  simp only [sum_assoc]
end LogicLineages.OrdinalComparison.Source.SourceUnaryChain.Proof
