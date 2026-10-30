module

public import LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupport
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! Actual arbitrary free-variable binding and guarded canonical selection.
The select map is not identity on source formula codes. Its semantic source
calibration requires the exact singleton free support {v}, not just card=1.
Binding itself preserves all other free names and is defined for every body. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedBinding
open GorbowSyntax GorbowFormulaSubstitution

def bindDictionary {n : Nat} (v : Fin n) (i : Fin n) : Term (n+1) :=
  if i=v then .var 0 else .var i.succ

def selectDictionary {n : Nat} (v : Fin n) (i : Fin n) : Term 1 :=
  if i=v then .var 0 else .zero

def bindAll {n : Nat} (v : Fin n) (φ : Formula n) : Formula n :=
  .all (substituteFormula (bindDictionary v) φ)
def bindEx {n : Nat} (v : Fin n) (φ : Formula n) : Formula n :=
  .ex (substituteFormula (bindDictionary v) φ)
def selectVariable {n : Nat} (v : Fin n) (φ : Formula n) : Formula 1 :=
  substituteFormula (selectDictionary v) φ

def assignAt {n : Nat} (ρ : Fin n → Nat) (v : Fin n) (x : Nat) (i : Fin n) : Nat :=
  if i=v then x else ρ i
end LogicLineages.ComputabilityKnowledge.GorbowNamedBinding
