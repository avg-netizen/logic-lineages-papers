module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
/-- Actual raw-head membership becomes the exact original encoded-head Fields
conjunct in the literal classCodes metadata list. All lists and metadata are
actual graph observations, not assumed enumerations or decoded images.
The paid sourceHead observation explicitly retains original raw-head validity;
no validity or inverse law for arbitrary malformed raw heads is asserted. -/
def InternalHeadAllowed : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param rawHead symbols types heads : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.symbols symbols seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)) →
  Nonempty (Derivation body Delta
    (OriginalGuardedHeadSourceCoverage.Targets.sourceHead n arity rawHead symbols types)) →
  Nonempty (Derivation body Delta (OriginalEnumerationFields.Targets.headAllowed n heads rawHead))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalSourceHeadsFieldsBridge.Targets
