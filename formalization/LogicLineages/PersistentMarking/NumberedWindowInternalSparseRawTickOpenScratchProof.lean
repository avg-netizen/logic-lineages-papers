module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open NumberedWindowInternalSparsePathEnvelopeTargets (z rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell packedReports)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalFreshProbeDispatchProgram (predOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawTick
open NumberedWindowInternalSparseRawTickTargets (stateTerm)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem frameRead (flag frame : OTerm α) :
    Nonempty (Derivation body Γ (unary stateFrame frame (stateTerm flag frame))) := by
  let rest := rawCons frame z
  let st := stateTerm flag frame
  obtain ⟨outer⟩ := canonicalCell (body := body) (Γ := Γ) flag rest
  obtain ⟨inner⟩ := canonicalCell (body := body) (Γ := Γ) frame z
  exact makeUnary cellHead cellTail frame st rest
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight inner)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight outer)⟩

theorem liveRead (flag q w r : OTerm α) :
    let frame := frameValueTerm q w r
    let st := stateTerm flag frame
    Nonempty (Derivation body Γ (unary stateFrame frame st)) ∧
    Nonempty (Derivation body Γ (unary rowSource q st)) ∧
    Nonempty (Derivation body Γ (unary rowWitness w st)) ∧
    Nonempty (Derivation body Γ (unary rowDestination r st)) := by
  let frame := frameValueTerm q w r
  let st := stateTerm flag frame
  let payload := packedBody [q,w,r]
  have exposed : Nonempty (Derivation body Γ (unary stateFrame frame st)) := frameRead flag frame
  have pred : Nonempty (Derivation body Γ (unary predOne payload frame)) := by
    rw [exact_DispatchControlAST.2.2.1]
    exact predecessorSuccessor payload
  have decoded : Nonempty (Derivation body Γ (unary rowBody payload st)) :=
    makeUnary predOne stateFrame payload st frame pred exposed
  have parts := packedReports st rowBody [q,w,r] decoded
  exact ⟨exposed,parts.1,parts.2.1,parts.2.2.1⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickOpenScratchProof
