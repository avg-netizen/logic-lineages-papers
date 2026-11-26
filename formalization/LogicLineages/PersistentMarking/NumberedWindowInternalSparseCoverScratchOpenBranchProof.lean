module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (coverOption optionPayload scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem payloadZero : Nonempty (Derivation body Γ (unary optionPayload z z)) :=
  zeroBranchIntro (.projection 0) (constantZero 1) predecessor z ![z]
    (projectionValue 0 ![z]) (zeroConstantValue ![z])

private theorem payloadSuccessor (value : OTerm α) :
    Nonempty (Derivation body Γ (unary optionPayload value (suc value))) :=
  successorBranchIntro (.projection 0) (constantZero 1) predecessor value value ![suc value]
    (projectionValue 0 ![suc value]) (predecessorSuccessor value)

private theorem scratchFromPayload (C : Program 3) (s : Settings) (tag seed value : OTerm α)
    (option : Nonempty (Derivation body Γ (unary (coverOption C s) tag seed)))
    (payload : Nonempty (Derivation body Γ (unary optionPayload value tag))) :
    Nonempty (Derivation body Γ (unary (scratchVertices C s) value seed)) := by
  apply compositionValue optionPayload (fun _ : Fin 1 => coverOption C s)
    value ![seed] ![tag] payload
  intro i
  obtain rfl := Fin.eq_zero i
  exact option

theorem scratchZero (C : Program 3) (s : Settings) (seed : OTerm α)
    (option : Nonempty (Derivation body Γ (unary (coverOption C s) z seed))) :
    Nonempty (Derivation body Γ (unary (scratchVertices C s) z seed)) :=
  scratchFromPayload C s z seed z option payloadZero

theorem scratchSuccessor (C : Program 3) (s : Settings) (value seed : OTerm α)
    (option : Nonempty (Derivation body Γ (unary (coverOption C s) (suc value) seed))) :
    Nonempty (Derivation body Γ (unary (scratchVertices C s) value seed)) :=
  scratchFromPayload C s (suc value) seed value option (payloadSuccessor value)

private theorem payloadFromScratch (C : Program 3) (s : Settings) (tag seed value : OTerm α)
    (option : Nonempty (Derivation body Γ (unary (coverOption C s) tag seed)))
    (vertices : Nonempty (Derivation body Γ (unary (scratchVertices C s) value seed))) :
    Nonempty (Derivation body Γ (unary optionPayload value tag)) := by
  apply compositionRecover optionPayload (fun _ : Fin 1 => coverOption C s)
    value ![seed] ![tag] vertices
  intro i
  obtain rfl := Fin.eq_zero i
  exact option

theorem sameScratchOutput (C : Program 3) (s : Settings)
    (tag left right leftVertices rightVertices : OTerm α)
    (leftOption : Nonempty (Derivation body Γ (unary (coverOption C s) tag left)))
    (rightOption : Nonempty (Derivation body Γ (unary (coverOption C s) tag right)))
    (leftRun : Nonempty (Derivation body Γ (unary (scratchVertices C s) leftVertices left)))
    (rightRun : Nonempty (Derivation body Γ (unary (scratchVertices C s) rightVertices right))) :
    Nonempty (Derivation body Γ (eqn leftVertices rightVertices)) :=
  valueUnique optionPayload leftVertices rightVertices ![tag]
    (payloadFromScratch C s tag left leftVertices leftOption leftRun)
    (payloadFromScratch C s tag right rightVertices rightOption rightRun)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
