module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.CompilerSyntaxProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.BooleanProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
open PolynomialGraphCompletion CanonicalGuardSelector GuardChildMeasureCompletion ComparisonProof

theorem compiledThreeWay : Targets.CompiledThreeWay := by
  intro D p _hD hp x y hx hy hyx
  simp only [compile_eq D p hp] at hx hy ⊢
  let n := leastFuel D p
  have ha := RunnerProof.runAdmission D p hp n
  have hstop := ((RunnerProof.leastFuelCorrect D p).2.2.2 hp).1
  have hterminal := terminalComparison D (run p n).1 ha hstop x y
    ((finish_terminal p n).trans hx) ((finish_terminal p n).trans hy) hyx
  have haccum := RunnerProof.accumulatedComparison D p hp n x y
    ((finish_accumulated p n).trans hx) ((finish_accumulated p n).trans hy)
  have horder : orderNat (wordValue p.1 x) (wordValue p.2 y) =
      liftTie (run p n).2.2
        (orderInt (RowValue (terminalRow (run p n).1) (pairEnv x y)) 0) :=
    haccum.trans (congrArg (liftTie (run p n).2.2) hterminal.2.2.2)
  have hguard (desired : Nat) (hd : desired ≤ 2) :
      GuardHolds (guardAt (packageGuards (finish p n)) desired)
        (packageRow (finish p n)) (pairEnv x y) ↔
      orderNat (wordValue p.1 x) (wordValue p.2 y) = desired := by
    change (∃ sign ∈ guardAt (makeGuards (run p n).2.2) desired,
      SignAtom sign (RowValue (terminalRow (run p n).1) (pairEnv x y))) ↔ _
    rw [booleanGuardsCorrect (run p n).2.2 desired _ hd,← horder]
  exact ⟨(orderNat_eq_zero _ _).symm.trans (hguard 0 (by omega)).symm,
    (orderNat_eq_one _ _).symm.trans (hguard 1 (by omega)).symm,
    (orderNat_eq_two _ _).symm.trans (hguard 2 (by omega)).symm⟩

theorem compiledSameVariable : Targets.CompiledSameVariable := by
  intro D p _hD hp x hx
  simp only [compile_eq D p hp] at hx ⊢
  let n := leastFuel D p
  have ha := RunnerProof.runAdmission D p hp n
  have hstop := ((RunnerProof.leastFuelCorrect D p).2.2.2 hp).1
  have hterminal := terminalSameVariable D (run p n).1 ha hstop x
    ((finish_terminal p n).trans hx)
  have haccum := RunnerProof.accumulatedComparison D p hp n x x
    ((finish_accumulated p n).trans hx) ((finish_accumulated p n).trans hx)
  exact haccum.trans (congrArg (liftTie (run p n).2.2) hterminal)

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
