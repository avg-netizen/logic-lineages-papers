module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalRepresentativeTag
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL least representative preserves the outer type on every
packed term and every finite window. Neither subtype closure nor membership
in the universe is assumed. This is an external semantic theorem only. -/
def ActualOriginalRepresentativeOuterType : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (q : NumberedRewriteReduction.Packed (Fin n) arity Gamma),
  (Nat.unpair (NumberedLeastCodeRepresentative.representativeCode symbols S q)).1 =
    NumberedLeastCodeRepresentative.typeNumber q.1

/-- The concrete wrappers preserve BOTH original representative functions on
all natural inputs, including failed decodes, arbitrary windows and targets
outside the universe. The old step program is unchanged. -/
def ActualOriginalRepresentativeWrapperCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (old : InternalQuotientEdgeChecker.Data),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table
    (withRepresentatives validity old)

/-- Independent input and output outer-tag graph witnesses must agree when
the actual validity leaf accepts and the actual wrapper produces its output.
This applies to arbitrary Program leaves, with no calibration premise. -/
def ActualOriginalRepresentativeTagsEqual : Prop :=
  ∀ (body : Positive (Fin 1)) (valid oldRepresentative : Program 1)
    (α : Type) (rawTag outTag out raw : OTerm α),
  Nonempty (Derivation body []
    ((representation valid oldRepresentative out raw).imp
      ((graph1 InternalUnpair.left rawTag raw ⊓
        graph1 InternalUnpair.left outTag out).imp (equal rawTag outTag))))

/-- In particular an OUTPUT outer-tag graph derives the RAW INPUT outer-tag
graph at the same symbolic tag, without a supplied raw-tag witness. The reverse
direction also holds. No semantic truth-to-derivability rule is introduced. -/
def ActualOriginalRepresentativeTagTransport : Prop :=
  ∀ (body : Positive (Fin 1)) (valid oldRepresentative : Program 1)
    (α : Type) (tag out raw : OTerm α),
  Nonempty (Derivation body []
    ((representation valid oldRepresentative out raw).imp
      ((graph1 InternalUnpair.left tag out).iff
        (graph1 InternalUnpair.left tag raw))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagTargets
