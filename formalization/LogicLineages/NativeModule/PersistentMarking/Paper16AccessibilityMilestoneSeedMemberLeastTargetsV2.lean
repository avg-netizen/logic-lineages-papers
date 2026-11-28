module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneFreshApplicationTargetsV2
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPackedLeastOnProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets

/-! Frozen statement, **not proved**: a seed that occurs in its own cover pool has a least class
representative under `packedLeastOn` (Fable B, 27 November 2026; item 2 of the continuation).

`packedLeastOn C E s` is `branch contextOption 0 (scratchMinimum (members E (poolAtSeed C s) …))`.
The zero round keeps the pool entries equal to the seed, every later round keeps a pool entry
that equals an entry of the previous round (the equality clause of `scanStep`, independent of
the edge program `E`), and `scratchMinimum` of a list with an occurrence is a successor. So
the law concerns visible code only: `rounds` (recursion on the open fuel `poolLength`), `pass`
and `scan` (list recursions), `headEq`, `minimumStep`. It needs no fact about the cover `C` or
the edge `E` beyond the three hypotheses.

What this law does not give is the third hypothesis itself, occurrence of the seed in the pool
computed by `C`; see `verification/local-fable-trio-2026-11-27/fableB/SEED-MEMBER-REPORT.md`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn)
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowScalarAlgorithm (Settings)
open Paper16AccessibilityMilestoneFreshApplicationTargetsV2 (leastSelectedAt)

/-- With a successful context option, the pool reported by the cover on the seed, and an
occurrence of the seed in that pool, the packed least program returns a successor. Arbitrary
cover, edge program, settings, body, context and open terms. -/
def SeedMemberLeast : Prop :=
  ∀ (C : Program 3) (E : Program 4) (s : Settings) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty seed tag pool : OTerm α),
    Nonempty (Derivation body Γ (programGraph contextOption (suc tag) ![ctx, ty, seed])) →
    Nonempty (Derivation body Γ (programGraph (poolAtSeed C s) pool ![ctx, ty, seed])) →
    Nonempty (Derivation body Γ (memberGraph pool seed)) →
    Nonempty (Derivation body Γ (leastSelectedAt (packedLeastOn C E s) ctx ty seed))

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2
