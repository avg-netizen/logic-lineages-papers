module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsTargets

/-- Uniform Computable closure of the UNCHANGED original radix-six atom map.
The parameter and actual formula code are runtime inputs of the same program.
The supplied payload program is an input to this supporting closure lemma;
concrete formula consumers must discharge it with their actual proven program.
No primitive-recursive strengthening or valid-code restriction is asserted. -/
def ActualJointMapProgram : Prop := ∀ (α : Type) [Primcodable α]
    (op : α → Nat → Nat), Computable₂ op →
  Computable₂ (fun args code => LinearRows.Code.mapAtoms (op args) code)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ComputableMapAtomsTargets
