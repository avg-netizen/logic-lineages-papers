module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGuardedOrdinaryListTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedMemoZeroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoClampProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases projectionValue valueUnique outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalCoverSelectedMemoZeroProof (exact_OpenCoverSelectedMemoZero)
open NumberedWindowInternalCoverArgumentMemoTargets (argumentMeasure argumentUpdate)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverGuardedOrdinaryListTargets

theorem exact_OpenCoverArgumentMemoClamp : ExactOpenCoverArgumentMemoClamp := by
  intro F body α Γ raw p actual
  let A := argumentMeasure F
  let C := selectedArgsMeasure A
  apply zeroSuccessorCases Γ raw (unary C p raw)
  · let E := eqn raw z
    let Δ := E :: Γ
    have eq : Derivation body Δ E := Derivation.hypothesis List.mem_cons_self
    have found := moveUnary A p raw z ⟨eq⟩ (withHyp actual E)
    have base := exact_OpenCoverSelectedMemoZero (argumentUpdate F) body α Δ
    have same := valueUnique A z p ![z] base found
    have atZero : Nonempty (Derivation body Δ (unary C z (z : OTerm α))) :=
      zeroBranchIntro (.projection 0) (constantZero 1) A z ![z] (projectionValue 0 ![z])
        (constantZeroValue ![z])
    have picked := outputTransport C z p ![z] same atZero
    exact moveUnary C p z raw ⟨symm eq⟩ picked
  · intro β j Δ prior keep e
    rw [unaryRename]
    have got := renameInto actual j Δ keep
    rw [unaryRename] at got
    obtain ⟨eq⟩ := e
    let x := p.relabel j
    let r := raw.relabel j
    have atKey := moveUnary A x r (suc prior) ⟨eq⟩ got
    have branch : Nonempty (Derivation body Δ (unary C x (suc prior))) :=
      successorBranchIntro (.projection 0) (constantZero 1) A x prior ![suc prior]
        (projectionValue 0 ![suc prior]) atKey
    exact moveUnary C x (suc prior) r ⟨symm eq⟩ branch

#print axioms exact_OpenCoverArgumentMemoClamp

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentMemoClampProof
