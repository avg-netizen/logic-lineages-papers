module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric

theorem conjunctionBool {k : Nat} (p q : Program k) (v : List.Vector Nat k) (a b : Bool)
    (hp : evaluate p v = a.toNat) (hq : evaluate q v = b.toNat) :
    evaluate (InternalAcceptance.conjunction p q) v = (a && b).toNat := by
  rw [OriginalHeadWindow.NativeProof.conjunctionValue,hp,hq]
  cases a <;> cases b <;> rfl

theorem nativeHeadMove : Targets.NativeHeadMove := by
  intro n arity symbols types f g base target
  let v : List.Vector Nat 6 := ofFn ![headNumber f,codeNumber base,headNumber g,codeNumber target,
    numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]
  have hw : evaluate (windowGuard n arity) v =
      (decide (NumberedFiniteUniverse.HeadInWindow arity symbols types (decodeHead f))).toNat :=
    OriginalHeadWindow.NativeProof.nativeWindow n arity symbols types f
  have hs : evaluate (sourceGuard n arity) v =
      (decide (g ∈ NumberedAuxiliaryEnumeration.sourceHeads arity symbols types)).toNat :=
    (OriginalSourceHeads.NativeProof.nativeSourceHeads n arity symbols types).2 g
  have hc : evaluate classGuard v =
      (decide (RecursiveComparison.headEquivalent (decodeHead f) (decodeHead g))).toNat :=
    OriginalHeadClass.NativeProof.nativeClassAndEquivalence.2 n f g
  have hp : evaluate permutationGuard v = (NumberedExchangeCode.argumentPermutation base target).toNat :=
    OriginalArgumentPermutation.NativeProof.nativeOriginal n base target
  exact conjunctionBool _ _ v _ _ (conjunctionBool _ _ v _ _ (conjunctionBool _ _ v _ _ hw hs) hc) hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.NativeProof
