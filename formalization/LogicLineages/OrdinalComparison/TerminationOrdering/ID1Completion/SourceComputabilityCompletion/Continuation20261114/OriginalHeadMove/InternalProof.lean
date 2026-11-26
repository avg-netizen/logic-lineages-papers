module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalOriginalUniformVertexPathSupportProof
open InternalAcceptanceConjunctionProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem internalAcceptance : Targets.InternalAcceptance := by
  intro n arity body alpha Delta f base g target symbols types
  let xs : Fin 6 → OTerm alpha := ![f,base,g,target,symbols,types]
  constructor
  · intro h
    obtain ⟨ha⟩ := conjunctionRecover
      (InternalAcceptance.conjunction (InternalAcceptance.conjunction (windowGuard n arity) (sourceGuard n arity)) classGuard)
      permutationGuard xs h
    obtain ⟨hb⟩ := conjunctionRecover (InternalAcceptance.conjunction (windowGuard n arity) (sourceGuard n arity))
      classGuard xs ⟨Derivation.conjunctionLeft ha⟩
    obtain ⟨hc⟩ := conjunctionRecover (windowGuard n arity) (sourceGuard n arity) xs ⟨Derivation.conjunctionLeft hb⟩
    obtain ⟨hw⟩ := ternaryRecover (OriginalHeadWindow.window n arity) (.projection 0) (.projection 4) (.projection 5)
      (numeral 1) f symbols types xs ⟨Derivation.conjunctionLeft hc⟩
      (projectionValue 0 xs) (projectionValue 4 xs) (projectionValue 5 xs)
    obtain ⟨hs⟩ := ternaryRecover (OriginalSourceHeads.member n arity) (.projection 2) (.projection 4) (.projection 5)
      (numeral 1) g symbols types xs ⟨Derivation.conjunctionRight hc⟩
      (projectionValue 2 xs) (projectionValue 4 xs) (projectionValue 5 xs)
    obtain ⟨he⟩ := binaryRecover OriginalHeadClass.equivalent (.projection 0) (.projection 2)
      (numeral 1) f g xs ⟨Derivation.conjunctionRight hb⟩ (projectionValue 0 xs) (projectionValue 2 xs)
    obtain ⟨hp⟩ := binaryRecover OriginalArgumentPermutation.check (.projection 1) (.projection 3)
      (numeral 1) base target xs ⟨Derivation.conjunctionRight ha⟩ (projectionValue 1 xs) (projectionValue 3 xs)
    exact ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction hw hs) he) hp⟩
  · rintro ⟨h⟩
    have hw := ternaryValue (OriginalHeadWindow.window n arity) (.projection 0) (.projection 4) (.projection 5)
      (numeral 1) f symbols types xs ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft (Derivation.conjunctionLeft h))⟩
      (projectionValue 0 xs) (projectionValue 4 xs) (projectionValue 5 xs)
    have hs := ternaryValue (OriginalSourceHeads.member n arity) (.projection 2) (.projection 4) (.projection 5)
      (numeral 1) g symbols types xs ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft (Derivation.conjunctionLeft h))⟩
      (projectionValue 2 xs) (projectionValue 4 xs) (projectionValue 5 xs)
    have he := binaryValue OriginalHeadClass.equivalent (.projection 0) (.projection 2)
      (numeral 1) f g xs ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft h)⟩ (projectionValue 0 xs) (projectionValue 2 xs)
    have hp := binaryValue OriginalArgumentPermutation.check (.projection 1) (.projection 3)
      (numeral 1) base target xs ⟨Derivation.conjunctionRight h⟩ (projectionValue 1 xs) (projectionValue 3 xs)
    exact conjunctionAccept _ _ xs (conjunctionAccept _ _ xs (conjunctionAccept _ _ xs hw hs) he) hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.InternalProof
