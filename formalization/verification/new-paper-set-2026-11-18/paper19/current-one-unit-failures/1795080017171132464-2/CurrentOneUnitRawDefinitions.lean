module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open RawSourceDAG (Code)

abbrev HeadInput := List Nat × Nat
abbrev SelectedInput := Nat × List Nat × Nat
/-- L code, optional L' code, selected literal size data, and linear row. -/
abbrev Packet := Nat × Option Nat × Coefficients × LinearCode

def lambdaCode (domain body : Nat) : Nat := 8*Nat.pair domain body+6

def slotIndex (selected old : Nat) : Nat :=
  if old < selected then old+1 else if old = selected then 0 else old

def selectedTable (selected : Nat) (Γ : List Nat) : List Nat :=
  (List.range Γ.length).map (slotIndex selected)

/-- Literal coded context permutation. The scope-aware rename keeps
internal binders intact and only relabels the actual free input names. -/
def moveCode (selected : Nat) (d : Code) : Option Code := do
  let σ ← d.1[selected]?
  let Γ := σ :: (d.1.take selected ++ d.1.drop (selected+1))
  return RawSourceDAG.Operations.renameCode Γ (selectedTable selected d.1) d

def codedMultiplier (selectedType : Nat) (v : List Nat) : Nat :=
  2 ^ (SyntaxCode.typeLevel selectedType+1) * (v.map OrdinalSyntax.partialSize).sum

def compileHead (p : AdmissibleSum.Policy) (x : HeadInput) : Option Packet := do
  let σ ← x.1.head?
  if 0 < SyntaxCode.typeLevel σ then do
    let τ ← SyntaxCode.check x.1 x.2
    let a ← CurrentTreeInputCoverage.compile x.1 x.2
    let u := lambdaCode 0 (CurrentTreeCode.expand (CurrentDecisionEmitter.liftCode 1 a))
    let h ← PolicyAssignment.assignmentCode p x.1 x.2
    let h' ← PolicyAssignment.assignmentCode p x.1 u
    let h₀ ← h.head?
    let d : Coefficients := (codedMultiplier σ h,codedMultiplier σ h',OrdinalSyntax.headFree h₀)
    return (lambdaCode σ x.2,if d.2.2 then none else some (lambdaCode σ u),d,
      equation (SyntaxCode.typeLevel τ) d)
  else none

def compileSelected (p : AdmissibleSum.Policy) (x : SelectedInput) : Option Packet := do
  let d ← CurrentTreeInputCoverage.compile x.2.1 x.2.2
  let a ← moveCode x.1 d
  compileHead p (a.1,CurrentTreeCode.expand a)

def literalPacket {Γ : List Ty} {σ τ : Ty}
    (a : OriginalTerm (σ :: Γ) τ) (d : Coefficients) : Packet :=
  (SyntaxCode.encodeTerm (OneUnit.first a),
    if d.2.2 then none else some (SyntaxCode.encodeTerm (OneUnit.second a)),
    d,equation τ.level d)

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
