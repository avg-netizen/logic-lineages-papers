module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ChildTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.PlainAwareStructuralClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DescentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atChild (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node child window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 lambdaConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 lambdaConstructor right rm rc)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (hchild : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child lc rc)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false left right context)) := by
  have hpair := andLeft hedge
  have hlg := andLeft (andRight hedge)
  have hrg := andLeft (andRight (andRight hedge))
  have he := andRight (andRight (andRight hedge))
  have hrec := (OriginalDecodedLambdaRecurrence.Proof.lambdaRecurrence n arity body alpha Delta
    left right lm rm lc rc node child window hlc hrc hpair hchild).mp he
  have hcg := OriginalExchangeBoundsPreservation.UnaryGuardProof.child false n left lm lc hlc hlg
  have hdg := OriginalExchangeBoundsPreservation.UnaryGuardProof.child false n right rm rc hrc hrg
  have hsmall := OriginalTypedEnumerationDepthBound.DescentProof.lambdaCode left lm lc hlc
  have hcedge : Nonempty (Derivation body Delta (edge n arity lc rc child window)) :=
    andIntro hchild (andIntro hcg (andIntro hdg (andRight (andRight hrec))))
  have htransfer := ChildTransferProof.fromBelow n arity false left lc rc child window context symbols types
    henv hcedge ih hsmall
  obtain ⟨heq⟩ := andLeft (andRight hrec)
  have hrc' := headTransport lambdaConstructor right rm lm ![rc] ⟨symm heq⟩ hrc
  exact PlainAwareStructuralClosureProof.lambda n arity
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    body alpha Delta left right lm lc rc context hlc hrc' hlg hrg htransfer
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
