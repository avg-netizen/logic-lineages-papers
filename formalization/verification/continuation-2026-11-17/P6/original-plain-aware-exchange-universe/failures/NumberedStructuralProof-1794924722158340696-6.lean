module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.OrdinaryAtChildProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralProof
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

theorem branch (extrasSide : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right label f g recorded base dest extraTypes extras otherExtras child window context symbols types : OTerm alpha)
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
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (PlainAwareStructuralDefinitions.Transfer n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      false left right context)) := by
  have hleft := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n left label f recorded base extraTypes extras hlc hlg
  have hright := OriginalRankedRootHeadMovePreservation.RootGuardProof.numbered n right label g recorded dest extraTypes otherExtras hrc hrg
  have hrelation := OriginalGuardedHeadEquality.EqualityProof.accepted n f g (andLeft hleft) (andLeft hright)
  obtain ⟨himp⟩ := andLeft hrelation
  obtain ⟨hencoded⟩ := hencoded
  have hhead : Nonempty (Derivation body Delta (eqn f g)) := ⟨Derivation.implicationElimination himp hencoded⟩
  have hlgc := OriginalExchangeBoundsPreservation.NumberedGuardProof.children n left label f recorded base extraTypes extras hlc hlg
  have hrgc := OriginalExchangeBoundsPreservation.NumberedGuardProof.children n right label g recorded dest extraTypes otherExtras hrc hrg
  have hsmall := OriginalTypedEnumerationDepthBound.DescentProof.numbered left label f recorded base extraTypes extras hlc
  have hcedge : Nonempty (Derivation body Delta (edge n arity
      (if extrasSide then extras else base) (if extrasSide then otherExtras else dest) child window)) := by
    cases extrasSide
    · exact andIntro hpair (andIntro (andLeft hlgc) (andIntro (andLeft hrgc) he))
    · exact andIntro hpair (andIntro (andRight hlgc) (andIntro (andRight hrgc) he))
  have hless : Nonempty (Derivation body Delta (InternalLessThan.strictLess (if extrasSide then extras else base) left)) := by
    cases extrasSide
    · exact andLeft hsmall
    · exact andRight hsmall
  have htransfer := ChildTransferProof.fromBelow n arity true left
    (if extrasSide then extras else base) (if extrasSide then otherExtras else dest) child window context symbols types henv hcedge ih hless
  have hrc' : Nonempty (Derivation body Delta (programGraph numberedConstructor right
      ![label,f,recorded,if extrasSide then base else dest,extraTypes,if extrasSide then otherExtras else extras])) := by
    apply NumberedInputProof.inputs right ![label,g,recorded,dest,extraTypes,otherExtras] _ hrc
    intro i
    fin_cases i
    · exact ⟨refl _⟩
    · exact hhead
    · exact ⟨refl _⟩
    · cases extrasSide
      · exact ⟨refl _⟩
      · exact hsibling
    · exact ⟨refl _⟩
    · cases extrasSide
      · exact hsibling
      · exact ⟨refl _⟩
  cases extrasSide
  · exact PlainAwareStructuralClosureProof.numberedBase n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      body alpha Delta left right label f recorded base dest extraTypes extras context hlc hrc' hlg hrg htransfer
  · exact PlainAwareStructuralClosureProof.numberedExtras n arity
      (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity)
      body alpha Delta left right label f recorded base extraTypes extras otherExtras context hlc hrc' hlg hrg htransfer
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.NumberedStructuralProof
