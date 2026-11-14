module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary

/-- Existence is concluded from actual PR suppliers, not assumed fields. -/
def SupplierSelection : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (C P : Program 2) (E : Program 3), SuppliersCalibrated n arity C P E

/-- Every original malformed/default branch and the literal vertices.length
cutoff are retained on all vectors. -/
def Calibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (T C P : Program 2) (E : Program 3),
  Membership.TargetCalibrated n arity T → SuppliersCalibrated n arity C P E →
  Membership.ListCalibrated n arity (primary T C P E)

/-- No native supplier correctness appears in this independent internal law. -/
def InternalSeedMembership : Prop := ∀ (T C P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta (graph2 (primary T C P E) out seed parameter)) →
  Nonempty (Derivation body Delta (graph2 Membership.contains (numeral 1) out seed))

/-- Actual class reflexivity at the same concrete L and D. No symmetry,
row coherence or equality with a previous chosen tuple is asserted. -/
def InternalClassReflexivity : Prop := ∀ (T C P : Program 2) (E : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed parameter : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 T (numeral 1) seed parameter)) →
  Nonempty (Derivation body Delta
    (graph3 (Membership.classTest T (primary T C P E) (TransparentCandidate.candidate T))
      (numeral 1) seed seed parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.Targets
