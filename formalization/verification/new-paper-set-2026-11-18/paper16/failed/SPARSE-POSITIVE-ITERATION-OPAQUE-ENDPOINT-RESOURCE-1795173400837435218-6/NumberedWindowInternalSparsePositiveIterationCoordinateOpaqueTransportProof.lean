module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueBranchProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueTransportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (iterateStep)
open NumberedWindowInternalSparsePositiveFoldTargets (stepGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationCoordinateThinGraphProof (Stable retained)
open NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueBranchProof (stepStable)

attribute [local irreducible] programGraph iterateStep

private theorem sameKept {α : Type} (k prior c ty start cert k' start' cert' : OTerm α)
    (i : Fin 6) (keep : retained i) :
    call6 k prior c ty start cert i = call6 k' prior c ty start' cert' i := by
  unfold retained at keep
  rcases keep with hit | hit | hit
  all_goals rw [hit] <;> rfl

theorem moveUnused {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (raw : Program 5) (least : Program 3)
    (out prior c ty k start cert k' start' cert' : OTerm α)
    (h : Nonempty (Derivation body Γ (stepGraph raw least out k prior c ty start cert))) :
    Nonempty (Derivation body Γ (stepGraph raw least out k' prior c ty start' cert')) := by
  have cut := stepStable raw least
  unfold Stable at cut
  unfold stepGraph at h ⊢
  exact cut body α Γ out (call6 k prior c ty start cert) (call6 k' prior c ty start' cert')
    (sameKept k prior c ty start cert k' start' cert') h

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueTransportProof
