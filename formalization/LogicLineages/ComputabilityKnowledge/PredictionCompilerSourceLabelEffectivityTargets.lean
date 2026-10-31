module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity.Targets
open Turing.PartrecToTM2 PredictionCompilerFinitePayloadCodec PredictionCompilerSourceLabelExplicitCodec

def DecodePrimitiveRecursive : Prop := Primrec decode
def AssemblyPrimitiveRecursive : Prop := Primrec (fun x : Nat × Nat × Quint Label => assemble x.1 x.2.1 x.2.2)
def InspectPrimitiveRecursive : Prop := Primrec inspect
def StructuralFoldPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α] (z : α)
  (step : Nat → Nat → Quint α → α),
  Primrec (fun p : Nat × Nat × Quint α => step p.1 p.2.1 p.2.2) → Primrec (termFold z step)
def FiniteTablePrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α],
  Primrec (gammaTable (α := α)) ∧ Primrec (tableGamma (α := α)) ∧
  Primrec (storeTable (α := α)) ∧ Primrec (tableStore (α := α))
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelEffectivity.Targets
