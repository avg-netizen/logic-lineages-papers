module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedMoveAtProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedExchangeCasesProof
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
open OriginalRawSyntaxTransport (numberedConstructor)
open Continuation20261114

theorem atValues (n : Nat) (arity : Fin n → Nat)
    (left right label lh rh lt rt lts rts lc ld rc rd node first last window symbols types cv dv ev fv lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,lh,lt,lc,lts,ld])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,rh,rt,rc,rts,rd])))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first lc rc)))
    (hlast : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last ld rd)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hcv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) cv lc)))
    (hdv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) dv rc)))
    (hev : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) ev ld)))
    (hfv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) fv rd)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  have hg := ExchangeGuardProof.accepted n arity node left right window hp he
  have hlg := andLeft hg
  have hrg := andRight hg
  have hr := (OriginalDecodedNumberedRecurrence.Proof.numberedRecurrence n arity body alpha Delta
    left right label label lh rh lt rt lc rc lts rts ld rd node first last window symbols types hlc hrc hp hfirst hlast hw).mp he
  let move := eqn ld rd ⊓ programGraph (OriginalHeadMove.headMove n arity) (suc z) ![lh,lc,rh,rc,symbols,types]
  let base := (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) lh rh ⊓ eqn ld rd) ⊓
    graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window
  let extra := (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) lh rh ⊓ eqn lc rc) ⊓
    graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window
  have choices : Nonempty (Derivation body Delta ((move ⊔ base) ⊔ extra)) := andRight (andRight hr)
  apply OriginalTypedDecoderInternalBranchProof.orCases choices
  · have inner : Nonempty (Derivation body ((move ⊔ base) :: Delta) (move ⊔ base)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply OriginalTypedDecoderInternalBranchProof.orCases inner
    · have hb : Nonempty (Derivation body (move :: (move ⊔ base) :: Delta) move) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact NumberedMoveAtProof.atValues n arity left right label lh rh lt rt lts rts lc ld rc rd symbols types cv dv ev lv rv
        (withHyp (withHyp hlc _) _) (withHyp (withHyp hrc _) _) (withHyp (withHyp hlg _) _) (withHyp (withHyp hrg _) _)
        (andRight hb) (andLeft hb) (withHyp (withHyp hcv _) _) (withHyp (withHyp hdv _) _)
        (withHyp (withHyp hev _) _) (withHyp (withHyp hlv _) _) (withHyp (withHyp hrv _) _)
    · have hb : Nonempty (Derivation body (base :: (move ⊔ base) :: Delta) base) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have ho := headTransport (OriginalCodeBoundsRecursion.bounds n) ev ld rd (fun i : Fin 0 => Fin.elim0 i)
        (andRight (andLeft hb)) (withHyp (withHyp hev _) _)
      exact NumberedExchangeAtProof.atValues false n arity left right label lh rh lt rt lts rts lc ld rc rd first window cv dv ev lv rv
        (withHyp (withHyp hlc _) _) (withHyp (withHyp hrc _) _) (withHyp (withHyp hlg _) _) (withHyp (withHyp hrg _) _)
        (withHyp (withHyp hfirst _) _) (andRight hb) (withHyp (withHyp hcv _) _) (withHyp (withHyp hdv _) _)
        (withHyp (withHyp hev _) _) ho (withHyp (withHyp hlv _) _) (withHyp (withHyp hrv _) _) (withHyp (withHyp ih _) _)
  · have hb : Nonempty (Derivation body (extra :: Delta) extra) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ho := headTransport (OriginalCodeBoundsRecursion.bounds n) cv lc rc (fun i : Fin 0 => Fin.elim0 i)
      (andRight (andLeft hb)) (withHyp hcv _)
    exact NumberedExchangeAtProof.atValues true n arity left right label lh rh lt rt lts rts lc ld rc rd last window ev fv cv lv rv
      (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _) (withHyp hlast _)
      (andRight hb) (withHyp hev _) (withHyp hfv _) (withHyp hcv _) ho
      (withHyp hlv _) (withHyp hrv _) (withHyp ih _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedExchangeCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedExchangeCasesProof
