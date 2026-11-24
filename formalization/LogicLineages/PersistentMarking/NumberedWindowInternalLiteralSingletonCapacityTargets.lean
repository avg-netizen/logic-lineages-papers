module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonScratchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)

abbrev observed {α : Type} (src joined : OTerm α) : Formula α :=
  programGraph permutation (suc z) ![src,joined]

/-- All reports on the *same* physical original ordered source split. -/
structure Held (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (src q kept removed joined : OTerm α) : Prop where
  singletonCount : Nonempty (Derivation B Γ (counted src q (suc z)))
  sourceAppend : Nonempty (Derivation B Γ (appendGraph joined kept removed))
  countObserved : Nonempty (Derivation B Γ (observed src joined))

/-- One actual removed member exhausts the source singleton capacity:
an independent actual kept occurrence contradicts the selected original
occurrence-count observer on the actual source ordered append.
The two queried keys need not be syntactically the same. -/
def ExactLiteralSingletonKeptAbsent : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (src q kept removed joined removedKey keptKey : OTerm α),
    Nonempty (Derivation B Γ (consGraph src q z)) →
    Nonempty (Derivation B Γ (memberGraph removed removedKey)) →
    Nonempty (Derivation B Γ (appendGraph joined kept removed)) →
    Nonempty (Derivation B Γ (observed src joined)) →
    Nonempty (Derivation B Γ (memberGraph kept keptKey).not)

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonCapacityTargets
