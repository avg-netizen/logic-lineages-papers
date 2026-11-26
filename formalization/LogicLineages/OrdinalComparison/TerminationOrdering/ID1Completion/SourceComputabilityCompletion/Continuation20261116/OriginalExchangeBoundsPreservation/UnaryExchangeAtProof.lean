module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeChildQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryBoundsCongruenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open ExchangeInduction ExchangeInductionBindingProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro)
open Continuation20261115
open OriginalCodeBoundsConstructors.UnaryValueProof (constructor)

theorem atValues (ordinary : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc child window cv dv lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 (constructor ordinary) right rm rc)))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child lc rc)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window)))
    (hcv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) cv lc)))
    (hdv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) dv rc)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hsmall : Nonempty (Derivation body Delta (InternalLessThan.strictLess lc left)) := by
    cases ordinary
    · exact OriginalTypedEnumerationDepthBound.DescentProof.lambdaCode left lm lc hlc
    · exact OriginalTypedEnumerationDepthBound.DescentProof.ordinary left lm lc hlc
  obtain ⟨heq⟩ := belowRawApply n arity left lc rc child window cv dv ih hsmall
    (andIntro hp (andIntro he (andIntro hcv hdv)))
  have hdv' := outputTransport (OriginalCodeBoundsRecursion.bounds n) dv cv ![rc] ⟨symm heq⟩ hdv
  exact UnaryBoundsCongruenceProof.sameChildValue ordinary n left right lm rm lc rc cv lv rv
    hlc hrc hlg hrg hcv hdv' hlv hrv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
