module
public import LogicLineages.PermittedControl.GroundComparisonReductionTargets
public import LogicLineages.PermittedControl.ClosedBlockDecisionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.GroundComparisonAssembly
open OrdinalComparison OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarCode)
open SelectedGeneratedSource (scalarValueWith)
open GroundScalarCircuit (Counter)

/-- The M4 interface of `opusA/GROUND-INTERFACE-FOR-M4.md`, for one raw
query compiler: on normalised scalar codes it emits the closed-block
arguments of a topological circuit with a plain matrix whose successful
observations are exactly the positive shared-input counterexamples. -/
def QueryInterface (query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args) : Prop :=
  ∀ (tag : Nat) {ι : Type} (index : ι → Nat) (sa sb : Scalar ι),
    ∃ (known : List Nat) (gs : List OriginalPrintedCircuitSequential.Gate) (p : NormalForm.Formula),
      OriginalPrintedCircuitSequential.Topological known gs ∧ PreparedProjection.PlainPreparedFormula p ∧
      query tag (scalarCode index sa) (scalarCode index sb) =
        OriginalPrintedRawFamilyFrontend.encodeInput known gs p true ∧
      ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
        (OriginalPrintedTypedExistential.HasSuccessfulObservation f gs p true ↔
          ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧
            Counter tag (scalarValueWith f (fun x => ν (index x)) sa) (scalarValueWith f (fun x => ν (index x)) sb))

/-- `thm:ground` from any computable query compiler meeting the interface,
with #261, M1, M3, the reduction and the unconditional closed-block decision. -/
def ExactGroundFromQuery : Prop :=
  ∀ query : Nat → Nat → Nat → OriginalPrintedRawFamilyFrontend.Args, QueryInterface query →
    Computable (fun x : Nat × Nat × Nat => query x.1 x.2.1 x.2.2) → GroundComparison.GroundComparison

end LogicLineages.PermittedControl.GroundComparisonAssembly
