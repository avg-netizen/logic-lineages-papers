module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.MaximumProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (refl symm)
open InternalAdditionLawsProof (add leftZero)
open InternalOriginalPairingOrderArithmeticProof (strictTransport)
open ArithmeticProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryGrowth (dl dr ls rs m : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (argumentsBound dl ls)))
    (hr : Nonempty (Derivation body Delta (argumentsBound dr rs)))
    (hm : Nonempty (Derivation body Delta
      (graph2 Continuation20261115.OriginalBoundsRecombination.maximum m dl dr))) :
    Nonempty (Derivation body Delta (termBound (suc m) (suc (add ls rs)))) := by
  have hleft := argumentsMonotone dl ls (add ls rs) hl
    (InternalUnpairArithmeticProof.leftWeakAdd ls rs)
  have hright := argumentsMonotone dr rs (add ls rs) hr
    (InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd ls rs)
  exact unaryGrowth m (add ls rs)
    (OriginalEnumerationMembership.MaximumProof.backward dl dr m (suc (twice (add ls rs))) hm hleft hright)

theorem positiveTailRoom (ls rs : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (InternalLessThan.strictLess z ls))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess (suc rs) (suc (add ls rs)))) := by
  have h := InternalOriginalPairingOrderArithmeticProof.addStrictRight z ls rs hp
  have h' := strictTransport rs (add ls rs) (add z rs) (add ls rs)
    ⟨symm (leftZero rs)⟩ ⟨refl _⟩ h
  exact OriginalEnumerationMembership.OrderProof.successorForward rs (add ls rs) h'

theorem tailTermBound (dr ls rs : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (InternalLessThan.strictLess z ls)))
    (hr : Nonempty (Derivation body Delta (argumentsBound dr rs))) :
    Nonempty (Derivation body Delta (termBound dr (add ls rs))) := by
  have room := doubleMonotone (suc rs) (add ls rs) (positiveTailRoom ls rs hp)
  have hstrict := strictTransport dr (twice (suc rs)) dr (suc (suc (twice rs)))
    ⟨refl _⟩ ⟨doubleSuccessor rs⟩ hr
  exact InternalSquareRootArithmeticSupportProof.rightSuccessor dr (twice (add ls rs))
    (InternalSquareRootArithmeticSupportProof.strictWeakTrans dr (twice (suc rs)) (twice (add ls rs)) hstrict room)

theorem consGrowth (dl dr ls rs m : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (InternalLessThan.strictLess z ls)))
    (hl : Nonempty (Derivation body Delta (termBound dl ls)))
    (hr : Nonempty (Derivation body Delta (argumentsBound dr rs)))
    (hm : Nonempty (Derivation body Delta
      (graph2 Continuation20261115.OriginalBoundsRecombination.maximum m dl dr))) :
    Nonempty (Derivation body Delta (argumentsBound (suc m) (add ls rs))) := by
  have hleft := termMonotone dl ls (add ls rs) hl
    (InternalUnpairArithmeticProof.leftWeakAdd ls rs)
  have hright := tailTermBound dr ls rs hp hr
  have hmax := OriginalEnumerationMembership.MaximumProof.backward dl dr m (twice (add ls rs)) hm hleft hright
  exact OriginalEnumerationMembership.OrderProof.successorForward m (suc (twice (add ls rs))) hmax
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryArithmeticProof
