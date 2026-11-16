module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedOrdinaryRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.HeadMoveBoundsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OrdinaryExchangeCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open ExchangeInduction
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261115
open OriginalRawSyntaxTransport (ordinaryConstructor)

open InternalTagArithmeticSupportProof (symm)
theorem atValues (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node child window symbols types cv dv lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 ordinaryConstructor right rm rc)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hchild : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child lc rc)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hcv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) cv lc)))
    (hdv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) dv rc)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hg := ExchangeGuardProof.accepted n arity node left right window hp he
  have hlg := andLeft hg
  have hrg := andRight hg
  have hr := (OriginalDecodedOrdinaryRecurrence.Proof.ordinaryRecurrence n arity body alpha Delta
    left right lm rm lc rc node child window symbols types hlc hrc hp hchild hw).mp he
  apply OriginalTypedDecoderInternalBranchProof.orCases (andRight hr)
  · have hb : Nonempty (Derivation body ((programGraph (Continuation20261114.OriginalHeadMove.headMove n arity) (suc z) ![lm,lc,rm,rc,symbols,types] ⊓
        graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (suc z) rm lm) :: Delta)
        (programGraph (Continuation20261114.OriginalHeadMove.headMove n arity) (suc z) ![lm,lc,rm,rc,symbols,types] ⊓
        graph2 OriginalDecodedOrdinaryRecurrence.resultEqual (suc z) rm lm)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hlchild := UnaryGuardProof.child true n left lm lc (withHyp hlc _) (withHyp hlg _)
    have hrchild := UnaryGuardProof.child true n right rm rc (withHyp hrc _) (withHyp hrg _)
    obtain ⟨hce⟩ := HeadMoveBoundsProof.preserved n arity lm lc rm rc symbols types cv dv
      (andLeft hb) hlchild hrchild (withHyp hcv _) (withHyp hdv _)
    have hdv' := outputTransport (OriginalCodeBoundsRecursion.bounds n) dv cv ![rc] ⟨symm hce⟩ (withHyp hdv _)
    exact UnaryBoundsCongruenceProof.sameChildValue true n left right lm rm lc rc cv lv rv
      (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp hcv _) hdv' (withHyp hlv _) (withHyp hrv _)
  · have hb : Nonempty (Derivation body ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) lm rm ⊓
        graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window) :: Delta)
        (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) lm rm ⊓
        graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact UnaryExchangeAtProof.atValues true n arity left right lm rm lc rc child window cv dv lv rv
      (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp hchild _)
      (andRight hb) (withHyp hcv _) (withHyp hdv _) (withHyp hlv _) (withHyp hrv _) (withHyp ih _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OrdinaryExchangeCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OrdinaryExchangeCasesProof
