module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- All input vectors and malformed-node default zero, not merely encoded images. -/
def NativeOriginalRank : Prop := ∀ (n : Nat) (v : List.Vector Nat 2),
  evaluate (rank n) v = Continuation20261114.ExchangeNumericSuppliers.rankValue n v
/-- Actual original rank graph outputs decrease along every actual concrete
supplier member. Parent/child coordinates and decoder success are internal
witnesses, not premises; this is not a raw-code-only rank surrogate. -/
def InternalRankDecrease : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node parameter out child parentRank childRank : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (OriginalDecodedDependencies.dependencies n) out node parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)) →
  Nonempty (Derivation body Delta (graph2 (rank n) parentRank node parameter)) →
  Nonempty (Derivation body Delta (graph2 (rank n) childRank child parameter)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess childRank parentRank))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.Targets
