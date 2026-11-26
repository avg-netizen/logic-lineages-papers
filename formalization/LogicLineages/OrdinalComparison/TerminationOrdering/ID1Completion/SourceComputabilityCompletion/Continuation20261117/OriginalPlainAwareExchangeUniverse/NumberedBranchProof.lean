module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedBranchProof
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
theorem move (n : Nat) (arity : Fin n → Nat)
    (left right label f g recorded base dest extraTypes extras otherExtras typ gamma window context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hsame : Nonempty (Derivation body Delta (eqn extras otherExtras)))
    (hmove : Nonempty (Derivation body Delta (programGraph (OriginalHeadMove.headMove n arity) (suc z) ![f,base,g,dest,symbols,types])))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have hrc' : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,extras])) := by
    apply NumberedInputProof.inputs right ![label,g,recorded,dest,extraTypes,otherExtras] _ hrc
    apply SixCoordinateProof.coordinate_relation
      (fun x y : OTerm alpha => Nonempty (Derivation body Delta (eqn x y)))
    · exact ⟨refl _⟩
    · exact ⟨refl _⟩
    · exact ⟨refl _⟩
    · exact ⟨refl _⟩
    · exact ⟨refl _⟩
    · exact hsame
  exact HeadLeafProof.numbered n arity left right label recorded extraTypes extras
    f g base dest typ gamma context symbols types window hlc hrc' hlg hrg henv hmove ha hp

theorem recursive (extrasSide : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right label f g recorded base dest extraTypes extras otherExtras child window typ gamma context symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,f,recorded,base,extraTypes,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hlg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) left)))
    (hrg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) right)))
    (hencoded : Nonempty (Derivation body Delta (graph2 OriginalDecodedOrdinaryRecurrence.encodedEqual (suc z) f g)))
    (hsibling : Nonempty (Derivation body Delta (eqn (if extrasSide then base else extras) (if extrasSide then dest else otherExtras))))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child
      (if extrasSide then extras else base) (if extrasSide then otherExtras else dest))))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity false typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity false typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity false typ right gamma context)) := by
  have ht := NumberedStructuralProof.branch extrasSide n arity left right label f g recorded base dest extraTypes extras otherExtras
    child window context symbols types hlc hrc hlg hrg hencoded hsibling hpair he henv ih
  exact PlainAwareStructuralBindingProof.transferApply n arity
    (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
    false left right typ gamma context ht ha hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedBranchProof
