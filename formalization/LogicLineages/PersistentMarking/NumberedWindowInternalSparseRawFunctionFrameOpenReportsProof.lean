module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (packedNode)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem termReports (dom cod fn arg : OTerm α) :
    let n := auxiliaryTerm dom cod fn arg
    Nonempty (Derivation body Γ (unary termShape (suc z) n)) ∧
      Reports body Γ n cellTail [dom,cod,fn,arg] := by
  let n := auxiliaryTerm dom cod fn arg
  have tag : Nonempty (Derivation body Γ (unary (literal 1 6) (numeral 6) n)) :=
    literalGraph 6 ![n]
  exact packedNode (literal 1 6) (numeral 6) [dom,cod,fn,arg] tag

theorem witnessReports (child : OTerm α) :
    let n := functionWitnessTerm child
    Nonempty (Derivation body Γ (unary witnessShape (suc z) n)) ∧
      Reports body Γ n cellTail [child] := by
  let n := functionWitnessTerm child
  have tag : Nonempty (Derivation body Γ (unary (literal 1 5) (numeral 5) n)) :=
    literalGraph 5 ![n]
  exact packedNode (literal 1 5) (numeral 5) [child] tag

theorem onTape (p : Program 1) (i : Fin 3) (o : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation body Γ (unary p o (xs i)))) :
    Nonempty (Derivation body Γ (programGraph (onRaw p i) o xs)) := by
  unfold onRaw
  apply compositionValue p (fun _ : Fin 1 => .projection i) o xs (![xs i] : Fin 1 → OTerm α) h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
