module
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Targets
open SourceTypedPorts ScalarCarrierAccounting OriginalDomain

def SharedBaseEmbeddings : Prop := ∀ (Γ : List Ty) (ops : List (Operator Γ)),
  (∀ τ, Function.Injective (fun x : Variable Γ τ => baseMap ops x)) ∧
  ∀ op : Operator Γ,
    (∀ τ, Function.Injective (fun x : Variable (op.privateContext ++ Γ) τ => headMap op ops x)) ∧
    (∀ τ, Function.Injective (fun x : Variable (context ops) τ => shiftVariable op.privateContext x)) ∧
    ∀ (τ : Ty) (x : Variable Γ τ),
      headMap op ops (shiftVariable op.privateContext x) =
        shiftVariable op.privateContext (baseMap ops x)

/-- Actual merged assignment pairs and ordered exact common-unit head trace.
No numerical invariance of arbitrary private-ground scalar observations. -/
def ExactMergedAssignments : Prop := ∀ (Γ : List Ty) (ops : List (Operator Γ)),
  (merged ops).length = ops.length ∧
  List.Forall₂ (fun t v => AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v)
    (terms ops) (vectors ops) ∧
  (vectors ops).map (fun v => unitValue (v 1)) = ops.map (fun op => unitValue (op.vector 1))

/-- Concrete one-lambda actual source from given actual heterogeneous inputs.
Every base name remains shared. This is not extraction of carriers from P. -/
def ActualMergedChain : Prop := ∀ (Γ : List Ty) (ops : List (Operator Γ)),
  ∃ v : OrdinalVector (context ops) 1,
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (SourceUnaryChain.chainSource (terms ops)) = some v ∧
    ∀ μ : Variable (context ops) .ground → Nat,
      expressionValue (UnitObservation.substitution μ) (v 1) =
        chargedSum (ops.map (fun op => unitValue (op.vector 1)))
end LogicLineages.OrdinalComparison.Source.HeterogeneousUnaryAssembly.Targets
