module
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleTargets
public import LogicLineages.OrdinalComparison.SourceTypedPortsProof
public import Mathlib.Data.List.GetD

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.Proof

open SourceGroundComponentEnvironment SourceMachineRawValuations SourceTypedPorts

private theorem positive_list_complete (Γ : List Ty) (hΓ : AllGround Γ)
    (ν : OrdinalComponent Γ → Nat) (hp : PositiveRaw ν) :
    ∃ xs : List Nat, xs.length = Γ.length ∧ positive xs = true ∧
      ∀ c, rawValuation xs c = ν c := by
  induction Γ with
  | nil =>
      refine ⟨[], rfl, rfl, ?_⟩
      rintro ⟨σ, x, j⟩
      cases x
  | cons σ Γ ih =>
      have hσ : σ = Ty.ground := hΓ σ (by simp)
      subst σ
      let tailν : OrdinalComponent Γ → Nat := fun c => ν ⟨c.1, .there c.2.1, c.2.2⟩
      have htail : AllGround Γ := fun σ h => hΓ σ (by simp [h])
      obtain ⟨xs, hlen, hpos, hx⟩ := ih htail tailν (fun c => hp _)
      refine ⟨ν ⟨Ty.ground, .here, 0⟩ :: xs, by simp [hlen], ?_, ?_⟩
      · change (decide (0 < ν ⟨Ty.ground, .here, 0⟩) && positive xs) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hp _, hpos⟩
      · rintro ⟨τ, x, j⟩
        cases x with
        | here =>
            have hj : j = 0 := Fin.eq_zero j
            subst j
            rfl
        | there x =>
            simpa only [rawValuation, variableIndex, List.getD_cons_succ] using hx ⟨τ, x, j⟩

theorem positiveCoverage : Targets.PositiveCoverage := by
  constructor
  · intro n xs hlen hp c
    have hall : ∀ a ∈ xs, 0 < a := by
      simpa only [positive, List.all_eq_true, decide_eq_true_eq] using hp
    have hi := SourceTypedPortsProof.typedVariableIndex.1
      (List.replicate n Ty.ground) c.1 c.2.1
    have hix : variableIndex c.2.1 < xs.length := by
      simpa only [List.length_replicate, hlen] using hi
    unfold rawValuation
    rw [List.getD_eq_getElem xs 0 hix]
    exact hall _ (List.getElem_mem hix)
  · intro n ν hp
    have hΓ : AllGround (List.replicate n Ty.ground) :=
      fun σ h => (List.mem_replicate.mp h).2
    obtain ⟨xs, hlen, hpos, hx⟩ := positive_list_complete _ hΓ ν hp
    exact ⟨xs, by simpa only [List.length_replicate] using hlen, hpos, hx⟩

end LogicLineages.OrdinalComparison.Source.SourceGammaCounterexample.Proof
