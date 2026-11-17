module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.LambdaAtChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.HeadLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.EqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114 Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atChild (n : Nat) (arity : Fin n → Nat)
    (left right f g base target node child window typ gamma context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left f base)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right g target)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (hchild : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base target)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have hpair := andLeft hedge
  have hlg := andLeft (andRight hedge)
  have hrg := andLeft (andRight (andRight hedge))
  have he := andRight (andRight (andRight hedge))
  have hw := andRight (andRight (andRight henv))
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n left f base hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.ordinary n right g target hrc hrg
  have hrec := (OriginalDecodedOrdinaryRecurrence.Proof.ordinaryRecurrence n arity body alpha Delta
    left right f g base target node child window symbols types hlc hrc hpair hchild hw).mp he
  apply OriginalTypedDecoderInternalBranchProof.orCases (andRight hrec)
  · let A := programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,target,symbols,types] ⊓
      graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (suc z) g f
    have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact HeadLeafProof.ordinary n arity left right f g base target typ gamma context symbols types window
      (withHyp hlc A) (withHyp hrc A) (withHyp hlg A) (withHyp hrg A) (withHyp henv A)
      (andLeft hA) (withHyp ha A) (withHyp hp A)
  · let A := graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g ⊓
      graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window
    have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hrelation := OriginalGuardedHeadEquality.EqualityProof.accepted n f g
      (withHyp (andLeft hleft) A) (withHyp (andLeft hright) A)
    obtain ⟨himp⟩ := andLeft hrelation
    obtain ⟨henc⟩ := andLeft hA
    have heq := Derivation.implicationElimination himp henc
    have hrc' := headTransport ordinaryConstructor right g f ![target] ⟨symm heq⟩ (withHyp hrc A)
    have hcedge : Nonempty (Derivation body (A :: Delta) (edge n arity base target child window)) :=
      andIntro (withHyp hchild A) (andIntro (withHyp (andRight hleft) A)
        (andIntro (withHyp (andRight hright) A) (andRight hA)))
    have hs := OriginalTypedEnumerationDepthBound.DescentProof.ordinary left f base (withHyp hlc A)
    have htransfer := ChildTransferProof.fromBelow n arity true left base target child window context symbols types
      (withHyp henv A) hcedge (withHyp ih A) hs
    have hparent := PlainAwareStructuralClosureProof.ordinaryBase n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      body alpha (A :: Delta) left right f base target context (withHyp hlc A) hrc'
      (withHyp hlg A) (withHyp hrg A) htransfer
    exact PlainAwareStructuralBindingProof.transferApply n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false left right typ gamma context hparent (withHyp ha A) (withHyp hp A)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
