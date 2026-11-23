module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero conjunction)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (coveredWindow contextPresent ownSeed)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem contextProjection (ctx ty seed : OTerm α) (i : Fin 1) :
    Nonempty (Derivation B Γ
      (programGraph (Program.projection 0) (((![ctx] : Fin 1 → OTerm α)) i) ![ctx,ty,seed])) := by
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![ctx,ty,seed]

/-- The original context Option is the literal parser of slot 0. Its
physical payload, including nil, is independent of the other two slots. -/
theorem exact_OpenUnrestrictedContextOptionMove (ctx ty seed ty' seed' out : OTerm α)
    (old : Nonempty (Derivation B Γ (programGraph contextOption out ![ctx,ty,seed]))) :
    Nonempty (Derivation B Γ (programGraph contextOption out ![ctx,ty',seed'])) := by
  have parsed : Nonempty (Derivation B Γ (unary parser out ctx)) :=
    compositionRecover parser (fun _ : Fin 1 => .projection 0) out ![ctx,ty,seed] ![ctx]
      old (contextProjection ctx ty seed)
  exact compositionValue parser (fun _ : Fin 1 => .projection 0) out ![ctx,ty',seed'] ![ctx]
    parsed (contextProjection ctx ty' seed')

private theorem ownAt (C : Program 3) (s : Settings) (ctx ty seed vertices : OTerm α)
    (cover : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices seed)))
    (hit : Nonempty (Derivation B Γ (memberGraph vertices seed))) :
    Nonempty (Derivation B Γ (programGraph (ownSeed C s) (suc z) ![ctx,ty,seed])) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  apply compositionValue scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,seed] hit
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

/-- Introduce the actual selected unrestricted covered window at its own
seed, using the exact context parse and physical ordered scratch reports. -/
theorem exact_OpenMeasuredUnrestrictedCoveredWindowIntro
    (C : Program 3) (s : Settings) (baseW : Program 3) (ctx ty seed payload vertices : OTerm α)
    (base : Nonempty (Derivation B Γ (windowAt baseW ctx ty seed)))
    (context : Nonempty (Derivation B Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (cover : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices seed)))
    (hit : Nonempty (Derivation B Γ (memberGraph vertices seed))) :
    Nonempty (Derivation B Γ (windowAt (coveredWindow C s baseW) ctx ty seed)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  have yes : Nonempty (Derivation B Γ (programGraph contextPresent (suc z) xs)) :=
    successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload xs context
      (oneConstantValue xs)
  have own := ownAt C s ctx ty seed vertices cover hit
  exact conjunctionAccept baseW (conjunction contextPresent (ownSeed C s)) xs base
    (conjunctionAccept contextPresent (ownSeed C s) xs yes own)

#print axioms exact_OpenUnrestrictedContextOptionMove
#print axioms exact_OpenMeasuredUnrestrictedCoveredWindowIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof
