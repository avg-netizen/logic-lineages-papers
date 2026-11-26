module
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGDefinitions
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source GroundEquivalence
/-- All free variables in context order; collisions are allowed for noninjective typed renamings. -/
def renamingCode : {Γ Θ : List Ty} → Renaming Γ Θ → List Nat
  | [], _, _ => []
  | _::Γ, _, r => variableIndex (r Variable.here) ::
      renamingCode (Γ:=Γ) (fun x => r (Variable.there x))
def renameIndex (k : Nat) (ρ : List Nat) (i : Nat) : Nat :=
  if i < k then i else k + ρ.getD (i-k) 0
def insertIndex (k i : Nat) : Nat := if i < k then i else i+1
/-- Malformed/non-variable payloads are preserved literally. Valid variable nodes have one index. -/
def renameNode (ρ : List Nat) (a : Node) : Node :=
  if a.2.2.1 = 0 ∧ a.2.2.2.length = 1 then
    (a.1,a.2.1,0,[renameIndex a.1.length ρ (a.2.2.2.getD 0 0)])
  else a
/-- Insertion always extends the prefix; only an exact variable payload has its index changed. -/
def insertNode (a : Node) : Node :=
  let args := if a.2.2.1 = 0 ∧ a.2.2.2.length = 1 then
      [insertIndex a.1.length (a.2.2.2.getD 0 0)] else a.2.2.2
  (a.1++[0],a.2.1,a.2.2.1,args)
def appendTable (a b : List Node) : List Node := b++a
def renameTable (ρ : List Nat) (as : List Node) : List Node := as.map (renameNode ρ)
def insertTable (as : List Node) : List Node := as.map insertNode
/-- Unchecked structural operation; typed compatibility is supplied in the exact theorem.
Checked external operations will separately reject malformed inputs/renaming tables. -/
def renameCode (Θ ρ : List Nat) (c : Code) : Code :=
  (Θ,renameTable ρ c.2.1,c.2.2.1,c.2.2.2)
end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.Operations
