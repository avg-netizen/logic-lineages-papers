module

public import LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCommonFuelProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetProof
open PredictionGame PredictionLearning PredictionUniformHistory PredictionCommonFuel
open PredictionCommonBudget PredictionBaselineGame PredictionCommonBudgetTargets

theorem commonFuelSearchPartrec : CommonFuelSearchPartrec := by
  have hc : Computable (fun x : (Code × Nat) × Nat => (x.1.1, x.1.2, x.2)) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hp : Computable (fun x : (Code × Nat) × Nat => commonFuelTest x.1.1 x.1.2 x.2) := by
    apply (PredictionCommonFuelProof.commonFuelTestPrimrec.to_comp.comp hc).of_eq
    intro x
    dsimp only
  exact Partrec.rfind hp.partrec.to₂

theorem commonFuelSearchTotal : CommonFuelSearchTotal := by
  intro v ht n
  obtain ⟨F, hF⟩ := PredictionCommonFuelProof.commonFuelEventuallySuccessful v ht n
  exact Nat.rfind_dom.mpr ⟨F, by simp [hF F le_rfl], fun {_} _ => trivial⟩

theorem computableSelectedFuel : ComputableSelectedFuel := by
  classical
  intro v ht
  have hd : ∀ n : Nat, ∃ s : Nat, s ∈ commonFuelSearch v n :=
    fun n => Part.dom_iff_mem.mp (commonFuelSearchTotal v ht n)
  choose b hb using hd
  have hp : Partrec (fun n => commonFuelSearch v n) :=
    commonFuelSearchPartrec.comp (Computable.const v |>.pair Computable.id).partrec
  exact ⟨b, hp.of_eq_tot hb, hb⟩

theorem actualCommonAvailableBudget : ActualCommonAvailableBudget := by
  intro v ht
  obtain ⟨b, hb, hmem⟩ := computableSelectedFuel v ht
  refine ⟨b, hb, fun k => ⟨k, ?_⟩⟩
  intro n hn xs hxs
  have htest : commonFuelTest v n (b n) = true :=
    (Part.mem_some_iff.mp (Nat.rfind_spec (hmem n))).symm
  have hsome := (PredictionCommonFuelProof.commonFuelTestExact v n (b n)).mp htest k hn xs hxs
  cases hmove : boundedMove (compileSelfHistory v k) (b n) xs with
  | none => simp [hmove] at hsome
  | some a =>
    rw [PredictionLearningProof.move_sound (compileSelfHistory v k) (ht k) (b n) xs a hmove]

end LogicLineages.ComputabilityKnowledge.PredictionCommonBudgetProof
