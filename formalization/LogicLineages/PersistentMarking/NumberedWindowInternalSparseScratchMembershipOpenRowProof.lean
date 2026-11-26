module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseScratchMembership

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem onHead (h previous k : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn h k))) :
    Nonempty (Derivation body Γ (programGraph headMatches (suc z) ![h,previous,k])) := by
  let xs : Fin 3 → OTerm α := ![h,previous,k]
  apply compositionValue equalityTest (![.projection 0,.projection 2] : Fin 2 → Program 3)
    (suc z) xs ![h,k] (equalityOfEqual h k same)
  intro i
  exact Fin.cases (projectionValue 0 xs)
    (Fin.cases (projectionValue 2 xs) (fun noIndex => Fin.elim0 noIndex)) i

theorem stepHit (h previous k : OTerm α)
    (same : Nonempty (Derivation body Γ (eqn h k))) :
    Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,previous,k])) :=
  successorBranchIntro headMatches (.projection 1) (constantOne 3) (suc z) z ![h,previous,k]
    (onHead h previous k same) (oneConstantValue ![h,previous,k])

/-- If the actual recursive bit is one, either real head comparison
branch keeps it one. No numerical cut is reflected internally. -/
theorem stepKeep (h k : OTerm α) :
    Nonempty (Derivation body Γ (programGraph memberStep (suc z) ![h,suc z,k])) := by
  apply optionGraphCases headMatches (![h,suc z,k] : Fin 3 → OTerm α) _
  · intro β j Δ _ zero
    simp only [tripleInputsRename,sucRelabel,zRelabel] at zero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,suc z,k.relabel j]
    exact zeroBranchIntro headMatches (.projection 1) (constantOne 3) (suc z) xs zero
      (projectionValue 1 xs)
  · intro β j Δ prior _ nonzero
    simp only [tripleInputsRename,sucRelabel,zRelabel] at nonzero
    simp only [graph3Rename,sucRelabel,zRelabel]
    let xs : Fin 3 → OTerm β := ![h.relabel j,suc z,k.relabel j]
    exact successorBranchIntro headMatches (.projection 1) (constantOne 3) (suc z) prior xs nonzero
      (oneConstantValue xs)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenRowProof
