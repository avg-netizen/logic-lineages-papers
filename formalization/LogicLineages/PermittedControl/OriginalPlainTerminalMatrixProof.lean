module
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixSnapshotProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalMixedTerminalTest (Test rowAnswer)

private theorem readOrdered (θ : Nat → Nat) (p : NormalForm.Formula) (tail : List Bool) :
    readBits p ((LinearRows.atoms p).map (atomAnswer θ) ++ tail) =
      some (rowAnswer θ p,tail) := by
  induction p generalizing tail with
  | truth => rfl
  | falsity => rfl
  | atom a => cases a <;> rfl
  | negative p ih =>
      simp only [LinearRows.atoms,readBits,ih,rowAnswer,bind,pure,Option.bind_some] <;> rfl
  | conjunction p q hp hq =>
      simp only [LinearRows.atoms,List.map_append,List.append_assoc,readBits,hp,hq,rowAnswer,bind,pure,Option.bind_some] <;> rfl
  | disjunction p q hp hq =>
      simp only [LinearRows.atoms,List.map_append,List.append_assoc,readBits,hp,hq,rowAnswer,bind,pure,Option.bind_some] <;> rfl

theorem exactPlainTerminalSuffix : ExactPlainTerminalSuffix := by
  intro f θ p plain positive
  have h := OriginalMixedTerminalTest.exactTerminalTestRead (.rows p) plain θ positive
  have bits : (snapshot θ p).map Prod.snd = (LinearRows.atoms p).map (atomAnswer θ) := by
    simp only [snapshot,List.map_map,Function.comp_def]
  have read : readBits p ((snapshot θ p).map Prod.snd) = some (rowAnswer θ p,[]) := by
    rw [bits]
    simpa only [List.append_nil] using readOrdered θ p []
  constructor
  · intro pol
    exact ⟨snapshot θ p,(exactPlainTerminalSnapshot f θ p plain _).mpr rfl,
      read.trans (congrArg (fun b => some (b,[])) (h.mpr pol))⟩
  · rintro ⟨values,rowsAt,accepted⟩
    have eq := (exactPlainTerminalSnapshot f θ p plain values).mp rowsAt
    subst values
    change readBits p ((snapshot θ p).map Prod.snd) = some (positive,[]) at accepted
    exact h.mp (congrArg Prod.fst (Option.some.inj (read.symm.trans accepted)))

end LogicLineages.PermittedControl.OriginalPlainTerminalMatrix
