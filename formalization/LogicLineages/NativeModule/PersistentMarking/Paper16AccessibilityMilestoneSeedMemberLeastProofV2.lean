module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

/-! Proof of the frozen
`Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2.SeedMemberLeast`
(Fable B2, 27 November 2026).

The five-layer derivation planned for this statement (minimum of a list with an occurrence, the
equality clause of `scanStep`, `pass`, the fuel induction over `rounds`, assembly) already exists
in the accepted tree: `exact_SeedEveryRound`, `exact_OpenMembersAtLength` and
`exact_OpenMemberHasBoundedMinimum` are assembled by
`NumberedWindowInternalLiteralLeastOnMembersProof.exact_OpenLeastOnFromSeed`, whose premises are
the successful context option, the cover graph `unary (scratchVertices C s) vertices seed`, and
the occurrence of the seed. The frozen statement differs in two presentational points only:
the pool is reported by `poolAtSeed C s` on the tape `![ctx, ty, seed]` (a composition of
`scratchVertices C s` with the projection of slot 2, undone here by `compositionRecover`), and
the conclusion is written `leastSelectedAt`, which unfolds to `hasLeastOn`. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneSeedMemberLeastProofV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalLiteralLeastOnMembersProof (hasLeastOn exact_OpenLeastOnFromSeed)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (leastSelectedAt)
open Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2

/-- The pool reported on the packed tape is the cover's scratch list of the seed. -/
private theorem poolIsCover (C : Program 3) (s : Settings) {body : Positive (Fin 1)} {α : Type}
    {Γ : List (Formula α)} (ctx ty seed pool : OTerm α)
    (run : Nonempty (Derivation body Γ (programGraph (poolAtSeed C s) pool ![ctx, ty, seed]))) :
    Nonempty (Derivation body Γ (unary (scratchVertices C s) pool seed)) := by
  have run' : Nonempty (Derivation body Γ (programGraph
      (.composition (scratchVertices C s) (fun _ : Fin 1 => (.projection 2 : Program 3))) pool
      ![ctx, ty, seed])) := run
  change Nonempty (Derivation body Γ (programGraph (scratchVertices C s) pool ![seed]))
  apply compositionRecover (scratchVertices C s) (fun _ : Fin 1 => (.projection 2 : Program 3))
    pool ![ctx, ty, seed] ![seed] run'
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![ctx, ty, seed]

/-- The conclusion of the frozen statement is the existing open-domain report. -/
private theorem leastSelectedIsHasLeastOn (C : Program 3) (E : Program 4) (s : Settings) {α : Type}
    (ctx ty seed : OTerm α) :
    leastSelectedAt (packedLeastOn C E s) ctx ty seed = hasLeastOn C E s ctx ty seed := rfl

theorem exact_SeedMemberLeast : SeedMemberLeast := by
  intro C E s body α Γ ctx ty seed tag pool parsed poolRun hit
  rw [leastSelectedIsHasLeastOn]
  exact exact_OpenLeastOnFromSeed C E s ctx ty seed tag pool parsed
    (poolIsCover C s ctx ty seed pool poolRun) hit

#print axioms exact_SeedMemberLeast

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneSeedMemberLeastProofV2
