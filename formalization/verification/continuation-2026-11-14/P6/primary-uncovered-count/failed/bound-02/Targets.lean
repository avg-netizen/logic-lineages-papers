module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram NumberedMultisetNumeric
open TwoSol20261113.CalibratedPrimary.Membership
/-- All numeric inputs; duplicates count individually and actual list codec
malformed/default behavior is retained. Native calibration is not reflection. -/
def NativeCount : Prop := ∀ pool reached : Nat,
  evaluate count (List.Vector.ofFn ![pool,reached]) =
    (((decodeNumbers pool).getD []).filter
      (fun candidate => decide (candidate ∉ (decodeNumbers reached).getD []))).length
/-- Initial potential is bounded by the literal raw pool length. -/
def InternalBound : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (pool reached remaining size : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 count remaining pool reached)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size pool)) →
  Nonempty (Derivation body Delta (bounded remaining size))
/-- Actual internal inclusion, not a native set hypothesis. -/
def InternalAntitone : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (pool left right leftCount rightCount : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included left right)) →
  Nonempty (Derivation body Delta (graph2 count leftCount pool left)) →
  Nonempty (Derivation body Delta (graph2 count rightCount pool right)) →
  Nonempty (Derivation body Delta (bounded rightCount leftCount))
/-- A genuinely new pool member forces strict decrease of the same finite
potential. Newness is an explicit internal negation, not failed proof search. -/
def InternalStrictDecrease : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha))
    (pool left right leftCount rightCount candidate : OTerm alpha),
  Nonempty (Derivation body Delta (PrimaryMonotonicity.included left right)) →
  Nonempty (Derivation body Delta (graph2 count leftCount pool left)) →
  Nonempty (Derivation body Delta (graph2 count rightCount pool right)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool candidate)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) left candidate).not) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) right candidate)) →
  Nonempty (Derivation body Delta
    (arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula rightCount leftCount)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Targets
