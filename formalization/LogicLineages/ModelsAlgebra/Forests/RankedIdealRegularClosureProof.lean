module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosureTargets
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealConstructorsStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.Proof
open RankedParse ProfileAutomatonEncoding RankedIdealRegular RankedIdealConstructors RankedGraphImage

theorem downwardStarExact : Targets.DownwardStarExact := by
  intro M n rules _ _ t
  letI : DecidableEq (starMachine M rules).State :=
    inferInstanceAs (DecidableEq (M.State × ((i : Fin n) → (rules i).side.State) × Bool))
  change (RankedIdealMachine.downwardMachine (starMachine M rules)).accept
    (machineRun (RankedIdealMachine.downwardMachine (starMachine M rules)) t) = true ↔ _
  rw [RankedIdealMachine.StatementChecks.languageExact (starMachine M rules) t]
  constructor
  · rintro ⟨u, htu, hu⟩
    exact ⟨u, (RankedIdealRegular.StatementChecks.starExact M n rules u).mp hu, htu⟩
  · rintro ⟨u, hu, htu⟩
    exact ⟨u, htu, (RankedIdealRegular.StatementChecks.starExact M n rules u).mpr hu⟩

theorem compiledLinearIdeal : Targets.CompiledLinearIdeal := by
  intro M n rules _ _ hM
  have he : language (downwardStar M rules) = linearPiece (allowed rules) (language M) :=
    funext (fun t => propext (downwardStarExact M n rules t))
  rw [he]
  exact RankedIdealConstructors.StatementChecks.linearPieceIdeal (allowed rules) (language M) hM
end LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularClosure.Proof
