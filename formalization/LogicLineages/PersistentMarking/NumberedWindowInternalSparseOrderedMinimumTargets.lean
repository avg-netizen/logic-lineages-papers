module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowClassAlgorithm
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodec (consCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathAdvanceTargets (encodeState)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseOrderedMinimum

/-- All original raw lists, including zero, malformed tails, duplicates,
and a real minimum zero. The ordered supplied pool is not a synthesized
class cover and is not deduplicated before the original List.min?. -/
def ExactAllInputOrderedPoolMinimum : Prop :=
  ∀ raw : Nat,
    evaluate orderedPoolMinimum (raw ::ᵥ nil) =
      encodeState ((unpack raw).bind (fun pool => pool.min?))

/-- A successful physical one-cell option update genuinely returns
the offered head or preserves the same successful previous value. -/
def ExactOpenOrderedMinimumStep : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (h prior k : OTerm α),
    let selected := programGraph minimumStep (suc k) ![h,prior]
    Nonempty (Derivation body Γ (selected.imp (eqn k h ⊔ eqn prior (suc k))))

/-- One genuine structural provenance step on the same decoded scratch
cons cell. The successful code is its actual head or the same successful
minimum of its actual tail. The premise is the original physical cons
graph, not an assertion that the arithmetic code comes from any window. -/
def ExactOpenScratchMinimumCons : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (code h t k : OTerm α),
    let cell := programGraph consCode code ![h,t]
    let selected := unary scratchMinimum (suc k) code
    let retained := unary scratchMinimum (suc k) t
    Nonempty (Derivation body Γ ((cell ⊓ selected).imp (eqn k h ⊔ retained)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumTargets
