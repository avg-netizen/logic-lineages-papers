module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphTargets
open CommonLayerSyntax NormalForm SourceTermGraph

def ExactAllocation : Prop := ∀ (start : Nat) (t : BaseTerm),
  0 < nodeCount t ∧ (allocated start t).Nodup ∧
  (∀ i, i ∈ allocated start t ↔ start ≤ i ∧ i < start + nodeCount t) ∧
  (Fresh start t → ∀ i ∈ allocated start t, i ∉ t.variables)

def ExactGraphSupport : Prop := ∀ (start : Nat) (t : BaseTerm) (i : Nat),
  i ∈ (graph start t).variables ↔ i ∈ t.variables ∨ i ∈ allocated start t

def OriginalGraphDomains : Prop := ∀ (start : Nat) (t : BaseTerm) (row : Row),
  row ∈ rows start t → ∀ ν : Nat → Nat,
    rowMeaningful row ν ∧ rowMeaningful (SourceTermGraph.negateRow row) ν

def GraphSoundness : Prop := ∀ (start : Nat) (t : BaseTerm) (ν : Nat → Nat),
  (graph start t).eval ν → ν (output start t) = t.value ν

def TotalGraphRealization : Prop := ∀ (start : Nat) (t : BaseTerm) (ν : Nat → Nat),
  Fresh start t → ∃ σ : Nat → Nat,
    (∀ i, i ∉ allocated start t → σ i = ν i) ∧
    (graph start t).eval σ ∧ σ (output start t) = t.value ν

def AllocatedNodeUniqueness : Prop :=
  ∀ (start : Nat) (t : BaseTerm) (ν σ : Nat → Nat),
    (∀ i ∈ t.variables, ν i = σ i) →
    (graph start t).eval ν → (graph start t).eval σ →
    ∀ i ∈ allocated start t, ν i = σ i

def ExactExistentialGraph : Prop := ∀ (start : Nat) (t : BaseTerm) (ν : Nat → Nat) (y : Nat),
  Fresh start t → (t.value ν = y ↔
    existsPrefix ν (allocated start t) (resultFormula start t y))

def InstructionCodeCalibration : Prop := ∀ t : BaseTerm,
  SourceTermGraph.Code.instructions t.encode = instructions t ∧
    (instructions t).length = nodeCount t

def RowMachineCalibration : Prop :=
  ∀ (t : BaseTerm) (start : Nat) (stack : List Nat) (prior : List NormalForm.Code.RowData),
    SourceTermGraph.Code.run (instructions t) (start, stack, prior) =
      (start + nodeCount t, output start t :: stack,
        prior ++ (rows start t).map rowData)

def LiteralGraphCompiler : Prop := ∀ (t : BaseTerm) (start : Nat),
  SourceTermGraph.Code.package t.encode start =
    Encodable.encode (output start t, (graph start t).encode)

def ActualNumericProgram : Prop :=
  Primrec SourceTermGraph.Code.instructions ∧ Primrec₂ SourceTermGraph.Code.run ∧
    Primrec₂ SourceTermGraph.Code.package

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphTargets
