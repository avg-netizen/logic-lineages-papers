module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open OriginalUniverseDecoderInternalAcceptance
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Full original term source Fields coverage. Actual source admission,
actual metadata/measure graphs, and the original subtype/size/label conditions
are the only premises. No raw validity, recursive Fields, child success,
image, native calibration, or semantic constructor oracle is assumed.
Gamma need not lie in the outer window; lambda must derive the original length increment internally. -/
def InternalTermFields : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param context types heads typ raw gamma count pair size maxLabel labels tupleBound : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)) →
  Nonempty (Derivation body Delta
    (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (TermAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc tupleBound))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc labels))) →
  Nonempty (Derivation body Delta
    (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound))

/-- Full original arguments source Fields coverage. Actual source admission,
actual metadata/measure graphs, and the original subtype/size/label conditions
are the only premises. No raw validity, recursive Fields, child success,
image, native calibration, or semantic constructor oracle is assumed.
The extra type-list conclusion pays original argumentTypes/argumentsLength, not a strengthened nil depth bound. -/
def InternalArgumentsFields : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (seed param context types heads argTypes raw gamma count pair size maxLabel labels tupleBound : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.context context seed param)) →
  Nonempty (Derivation body Delta (graph2 OriginalClassCodes.types types seed param)) →
  Nonempty (Derivation body Delta (graph2 (OriginalClassCodes.heads n arity) heads seed param)) →
  Nonempty (Derivation body Delta
    (Continuation20261114.WindowSourceHeadInclusion.ArrowClosed types)) →
  Nonempty (Derivation body Delta
    (ArgumentsAccepted H (OriginalUniverseDomainCoverage.member n)
      (OriginalGuardedHeadSourceCoverage.window n arity) argTypes raw gamma context)) →
  Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)) →
  Nonempty (Derivation body Delta
    (graph1 (Continuation20261115.OriginalCodeBoundsRecursion.bounds n) pair raw)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair size maxLabel)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess size (suc tupleBound))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess maxLabel (suc labels))) →
  Nonempty (Derivation body Delta
    (OriginalEnumerationFields.Targets.accepted n raw count types heads labels tupleBound ⊓
      OriginalEnumerationFields.Targets.typesAllowed argTypes types tupleBound))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.Targets
