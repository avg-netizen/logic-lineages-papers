module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveClassesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnFixedPointProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveLeastStabilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalLiteralLeastOnFixedPointProof
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnCoverageProof (exact_OpenLeastOnFromCoverage)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename hasOnRename)
open NumberedWindowInternalLiteralRoundObserverTargets (observe Preserves)
open NumberedWindowInternalLiteralRoundObserverSyntaxProof (observeRename)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename CanReverse)
open NumberedWindowInternalLiteralEdgeOnCoverProof (KeepsCover)
open NumberedWindowInternalLiteralChildGuardEdgeProof
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast fullAuxiliaryDecorator)
open NumberedWindowInternalLiteralTypedRecursiveClassesProof
open NumberedWindowInternalLiteralTypedAuxEdgeGuardProof (typedAuxEdgeGuard)
open NumberedWindowInternalLiteralTypedAuxEdgeIntroProof (exact_OpenTypedAuxEdgeBase)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Actual guarded output is preserved across the physical edge: both
least queries are discharged from their covered endpoints, then their
positive guarded values are checked by the actual round observers. -/
theorem exact_OpenChildGuardedLeastPreserves (C : Program 3) (G : Program 4) (s : Settings)
    (endpoints : CoveredEndpoints C s G)
    (checked : ∀ O ∈ childGuardObservers, Preserves G O)
    (preservesLeast : Preserves G (packedLeastOn C G s)) :
    Preserves G (childGuardedLeast (packedLeastOn C G s)) := by
  intro B α Γ ctx ty a b value edge read
  obtain ⟨ca,cb⟩ := endpoints B α Γ ctx ty a b edge
  have start := exact_OpenLeastOnFromCoverage C G s ctx ty a ca
  have finish := exact_OpenLeastOnFromCoverage C G s ctx ty b cb
  apply casesLeastOn C G s ctx ty a _ start
  intro β j Δ x keep actual
  rw [observeRename]
  have moved := renameInto edge j Δ keep
  rw [edgeRename] at moved
  have prior := renameInto read j Δ keep
  rw [observeRename] at prior
  have covered := renameInto finish j Δ keep
  rw [hasOnRename] at covered
  apply casesLeastOn C G s (ctx.relabel j) (ty.relabel j) (b.relabel j) _ covered
  intro γ n Θ y stay dest
  rw [observeRename]
  have source := renameInto actual n Θ stay
  rw [leastOnRename] at source
  have arc := renameInto moved n Θ stay
  rw [edgeRename] at arc
  have requested := renameInto prior n Θ stay
  rw [observeRename] at requested
  let c := (ctx.relabel j).relabel n
  let t := (ty.relabel j).relabel n
  let q := (a.relabel j).relabel n
  let r := (b.relabel j).relabel n
  let w := (value.relabel j).relabel n
  let L := packedLeastOn C G s
  let K := childGuardedLeast L
  have left := exact_OpenChildGuardLeast C G s checked c t q (x.relabel n) source
  have right := exact_OpenChildGuardLeast C G s checked c t r y dest
  have real : D B Θ (observe L c t r (suc (x.relabel n))) :=
    preservesLeast B γ Θ c t q r (suc (x.relabel n)) arc source
  have eq := valueUnique L (suc y) (suc (x.relabel n)) ![c,t,r] dest real
  have same := valueUnique K (suc (x.relabel n)) w ![c,t,q] left requested
  exact outputTransport K (suc (x.relabel n)) w ![c,t,r] same
    (outputTransport K (suc y) (suc (x.relabel n)) ![c,t,r] eq right)

/-- This form has no separately assumed scalar stability. A concrete
memoized edge would supply its physical unfolding, reversal and coverage;
the checked original rounds then discharge both least and class observers. -/
theorem exact_OpenRecursiveDiagonalFromRounds (count : CountLengthBound) (strict : InternalStrictDecrease)
    (C : Program 3) (Base G : Program 4) (s : Settings)
    (unfolding : TypedEdgeRefines G (typedAuxEdgeGuard Base G))
    (guards : ∀ O ∈ childGuardObservers, Preserves Base O)
    (reverse : CanReverse G) (sameCover : KeepsCover C s G) (endpoints : CoveredEndpoints C s G)
    (ctx ty q k : OTerm α) (actual : D B Γ (leastOnGraph C G s ctx ty q k)) :
    D B Γ (programGraph (guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C G s))))
      (suc k) ![ctx,ty,q]) := by
  have projects : TypedEdgeRefines G Base := by
    intro B α Γ c t a b h
    exact exact_OpenTypedAuxEdgeBase Base G c t a b (unfolding B α Γ c t a b h)
  have installed : ∀ O ∈ childGuardObservers, Preserves G O := fun O mem =>
    exact_OpenTypedObserverRefines G Base O projects (guards O mem)
  have stable := exact_OpenLeastOnPreserves count strict C G s reverse sameCover endpoints
  exact exact_OpenTypedRecursiveFilteredLeast C Base G s unfolding guards
    (exact_OpenChildGuardedLeastPreserves C G s endpoints installed stable) ctx ty q k actual

#print axioms exact_OpenChildGuardedLeastPreserves
#print axioms exact_OpenRecursiveDiagonalFromRounds
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedRecursiveLeastStabilityProof
