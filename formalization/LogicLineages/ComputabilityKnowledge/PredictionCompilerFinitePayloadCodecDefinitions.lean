module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivityProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec
open Turing.PartrecToTM2
abbrev Quad (α : Type) := α × α × α × α
abbrev Quint (α : Type) := α × α × α × α × α

def gammaBits : Γ' → Bool × Bool
  | .consₗ => (false, false)
  | .cons => (false, true)
  | .bit0 => (true, false)
  | .bit1 => (true, true)
def bitsGamma : Bool × Bool → Γ'
  | (false, false) => .consₗ
  | (false, true) => .cons
  | (true, false) => .bit0
  | (true, true) => .bit1

def stackBits : K' → Bool × Bool
  | .main => (false, false)
  | .rev => (false, true)
  | .aux => (true, false)
  | .stack => (true, true)
def bitsStack : Bool × Bool → K'
  | (false, false) => .main
  | (false, true) => .rev
  | (true, false) => .aux
  | (true, true) => .stack

/-- Explicit finite function tables, not function-space enumeration. -/
def gammaTable {α : Type} (f : Γ' → α) : Quad α :=
  (f .consₗ, f .cons, f .bit0, f .bit1)
def tableGamma {α : Type} (t : Quad α) : Γ' → α
  | .consₗ => t.1
  | .cons => t.2.1
  | .bit0 => t.2.2.1
  | .bit1 => t.2.2.2

def storeTable {α : Type} (f : Option Γ' → α) : Quint α :=
  (f none, f (some .consₗ), f (some .cons), f (some .bit0), f (some .bit1))
def tableStore {α : Type} (t : Quint α) : Option Γ' → α
  | none => t.1
  | some .consₗ => t.2.1
  | some .cons => t.2.2.1
  | some .bit0 => t.2.2.2.1
  | some .bit1 => t.2.2.2.2
end LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec
