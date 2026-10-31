module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProductTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealConstructors

private theorem calibration (o : Operation) (M N : Machine) t :
    machineRun (productMachine o M N) t =
      (machineRun M t, machineRun N t, rootFlag o M N t) := by
  induction t with
  | atom => rfl
  | node p l r ihl ihr =>
      change (productMachine o M N).node p (machineRun (productMachine o M N) l)
        (machineRun (productMachine o M N) r) = _
      rw [ihl, ihr]
      rfl

theorem productExact : Targets.ProductExact := by
  intro o M N t
  change (machineRun (productMachine o M N) t).2.2 = true ↔ _
  rw [calibration o M N t]
  cases t <;> simp [rootFlag, language, and_assoc]

theorem downwardProductExact : Targets.DownwardProductExact := by
  intro o M N _ _ t
  letI : DecidableEq (productMachine o M N).State :=
    inferInstanceAs (DecidableEq (M.State × N.State × Bool))
  change (RankedIdealMachine.downwardMachine (productMachine o M N)).accept
    (machineRun (RankedIdealMachine.downwardMachine (productMachine o M N)) t) = true ↔ _
  rw [RankedIdealMachine.StatementChecks.languageExact (productMachine o M N) t]
  constructor
  · rintro ⟨u, htu, hu⟩
    obtain ⟨l, r, rfl, hl, hr⟩ := (productExact o M N u).mp hu
    exact ⟨.node o l r, ⟨l, r, hl, hr, rfl⟩, htu⟩
  · rintro ⟨u, ⟨l, r, hl, hr, rfl⟩, htu⟩
    exact ⟨.node o l r, htu, (productExact o M N _).mpr ⟨l, r, rfl, hl, hr⟩⟩
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularProduct.Proof
