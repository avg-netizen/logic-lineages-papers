module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open Continuation20261115 Continuation20261116
open OriginalRawSyntaxTransport Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open Continuation20261114
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right label f g recorded base dest extraTypes extras otherExtras first last typ gamma window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hfirst : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first base dest)))
    (hlast : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last extras otherExtras)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma)))
    (hcases : Nonempty (Derivation body Delta (((eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,dest,symbols,types]) ⊔ ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g ⊓ eqn extras otherExtras) ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window)) ⊔ ((graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g ⊓ eqn base dest) ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window)))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  let A := eqn extras otherExtras ⊓ programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,dest,symbols,types]
  let B := (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g ⊓ eqn extras otherExtras) ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) first window
  let C := (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g ⊓ eqn base dest) ⊓ graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) last window
  apply OriginalTypedDecoderInternalBranchProof.orCases hcases
  · have hAB : Nonempty (Derivation body ((A ⊔ B) :: Delta) (A ⊔ B)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply OriginalTypedDecoderInternalBranchProof.orCases hAB
    · have hA : Nonempty (Derivation body (A :: (A ⊔ B) :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact NumberedBranchProof.move n arity left right label f g recorded base dest extraTypes extras otherExtras
        typ gamma window context symbols types
        (withHyp (withHyp hlc _) _) (withHyp (withHyp hrc _) _)
        (withHyp (withHyp hlg _) _) (withHyp (withHyp hrg _) _) (andLeft hA) (andRight hA)
        (withHyp (withHyp henv _) _) (withHyp (withHyp ha _) _) (withHyp (withHyp hp _) _)
    · have hB : Nonempty (Derivation body (B :: (A ⊔ B) :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      exact NumberedBranchProof.recursive false n arity left right label f g recorded base dest extraTypes extras otherExtras
        first window typ gamma context symbols types
        (withHyp (withHyp hlc _) _) (withHyp (withHyp hrc _) _)
        (withHyp (withHyp hlg _) _) (withHyp (withHyp hrg _) _)
        (andLeft (andLeft hB)) (andRight (andLeft hB)) (withHyp (withHyp hfirst _) _) (andRight hB)
        (withHyp (withHyp henv _) _) (withHyp (withHyp ih _) _) (withHyp (withHyp ha _) _) (withHyp (withHyp hp _) _)
  · have hC : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact NumberedBranchProof.recursive true n arity left right label f g recorded base dest extraTypes extras otherExtras
      last window typ gamma context symbols types (withHyp hlc _) (withHyp hrc _) (withHyp hlg _) (withHyp hrg _)
      (andLeft (andLeft hC)) (andRight (andLeft hC)) (withHyp hlast _) (andRight hC)
      (withHyp henv _) (withHyp ih _) (withHyp ha _) (withHyp hp _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedCasesProof
