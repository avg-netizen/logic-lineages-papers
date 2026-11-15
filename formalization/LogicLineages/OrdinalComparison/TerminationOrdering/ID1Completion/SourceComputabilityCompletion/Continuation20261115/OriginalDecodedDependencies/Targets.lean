module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Every original encoded-node input, including failed decodes/default [], and
all parameters. No assumed input calibration or decoded witness. -/
def NativeOriginalSupplier : Prop := ∀ (n : Nat) (v : List.Vector Nat 2),
  evaluate (dependencies n) v = Continuation20261114.ExchangeNumericSuppliers.depsValue n v
/-- An actual rejected code guard on either coordinate forces the actual empty
numeric dependency list. No native evaluation is reflected internally. -/
def InternalRejectedEmpty : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (node parameter left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)) →
  (Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 0) left)) ∨
   Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (numeral 0) right))) →
  Nonempty (Derivation body Delta (graph2 (dependencies n) (numeral 0) node parameter))
/-- Every actual output member decreases both original raw-code coordinates;
all guard branches and the empty-output impossibility are discharged internally. -/
def InternalDependencyDescent : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node parameter left right out child childLeft childRight : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)) →
  Nonempty (Derivation body Delta (graph2 (dependencies n) out node parameter)) →
  Nonempty (Derivation body Delta (graph2 contains (numeral 1) out child)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childLeft childRight)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess childLeft left ⊓
    InternalLessThan.strictLess childRight right))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedDependencies.Targets
