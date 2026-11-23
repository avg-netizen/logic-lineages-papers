module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalScratchInclusionThinProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive arithmeticEmbedding)
open ID1Completion.InternalCalculus (Formula Derivation)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationCertificateConstructors (graph2)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalThinUncoveredCount (count bounded)
open NumberedWindowInternalScratchInclusionThinProof (included)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
/-- Actual internal inclusion, not a native set hypothesis. -/
def InternalAntitone : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (pool left right leftCount rightCount : OTerm alpha),
  Nonempty (Derivation body Delta (included left right)) →
  Nonempty (Derivation body Delta (graph2 count leftCount pool left)) →
  Nonempty (Derivation body Delta (graph2 count rightCount pool right)) →
  Nonempty (Derivation body Delta (bounded rightCount leftCount))
/-- A genuinely new pool member forces strict decrease of the same finite
potential. Newness is an explicit internal negation, not failed proof search. -/
def InternalStrictDecrease : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (pool left right leftCount rightCount candidate : OTerm alpha),
  Nonempty (Derivation body Delta (included left right)) →
  Nonempty (Derivation body Delta (graph2 count leftCount pool left)) →
  Nonempty (Derivation body Delta (graph2 count rightCount pool right)) →
  Nonempty (Derivation body Delta (graph2 scratchMember (numeral 1) pool candidate)) →
  Nonempty (Derivation body Delta (graph2 scratchMember (numeral 1) left candidate).not) →
  Nonempty (Derivation body Delta (graph2 scratchMember (numeral 1) right candidate)) →
  Nonempty (Derivation body Delta
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula rightCount leftCount)))
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountTargets
