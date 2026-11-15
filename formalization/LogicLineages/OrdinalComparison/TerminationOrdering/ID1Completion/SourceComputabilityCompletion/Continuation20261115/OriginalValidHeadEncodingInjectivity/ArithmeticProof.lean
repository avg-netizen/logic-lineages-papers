module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaPairArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.ArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (z suc eqn dbl)
open InternalTagArithmeticSupportProof (trans symm cancelSuc congSuc zeroNeSuc sucNeZeroApply)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
def even (t : OTerm alpha) : OTerm alpha := OrdinaryArithmetic.addTerm t t
def odd (t : OTerm alpha) : OTerm alpha := suc (even t)
def code (tag : Fin 6) (payload : OTerm alpha) : OTerm alpha :=
  match tag.val with
  | 0 => even z
  | 1 => even (suc z)
  | 2 => odd (even payload)
  | 3 => odd (odd (even payload))
  | 4 => odd (odd (odd (even payload)))
  | _ => odd (odd (odd (odd payload)))
def doubleToEven (t : OTerm alpha) : Derivation body Delta (eqn (dbl t) (even t)) :=
  InternalBetaPairArithmeticProof.twoMul t
def evenCancel {s t : OTerm alpha} (h : Derivation body Delta (eqn (even s) (even t))) :
    Derivation body Delta (eqn s t) := by
  have hc := InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.conjunctionLeft (InternalTagArithmeticProof.everyPair body s t)) Delta
  exact Derivation.implicationElimination hc
    (trans (doubleToEven s) (trans h (symm (doubleToEven t))))
def oddCancel {s t : OTerm alpha} (h : Derivation body Delta (eqn (odd s) (odd t))) :
    Derivation body Delta (eqn s t) := evenCancel (cancelSuc h)
def evenOddFalse {s t : OTerm alpha} (h : Derivation body Delta (eqn (even s) (odd t))) :
    Derivation body Delta ⊥ := by
  have hc := InternalPositiveUnfoldingSupportProof.weakenClosed
    (Derivation.conjunctionLeft (Derivation.conjunctionRight (InternalTagArithmeticProof.everyPair body s t))) Delta
  exact Derivation.implicationElimination hc
    (trans (doubleToEven s) (trans h (congSuc (symm (doubleToEven t)))))
def oddEvenFalse {s t : OTerm alpha} (h : Derivation body Delta (eqn (odd s) (even t))) :
    Derivation body Delta ⊥ := evenOddFalse (symm h)
theorem different (i j : Fin 6) (s t : OTerm alpha) (hne : i ≠ j)
    (h : Derivation body Delta (eqn (code i s) (code j t))) : Nonempty (Derivation body Delta ⊥) := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hne rfl)
  · exact ⟨zeroNeSuc (evenCancel h)⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨sucNeZeroApply (evenCancel h)⟩
  · exact False.elim (hne rfl)
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨evenOddFalse h⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse h⟩
  · exact False.elim (hne rfl)
  · exact ⟨evenOddFalse (oddCancel h)⟩
  · exact ⟨evenOddFalse (oddCancel h)⟩
  · exact ⟨evenOddFalse (oddCancel h)⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse (oddCancel h)⟩
  · exact False.elim (hne rfl)
  · exact ⟨evenOddFalse (oddCancel (oddCancel h))⟩
  · exact ⟨evenOddFalse (oddCancel (oddCancel h))⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse (oddCancel h)⟩
  · exact ⟨oddEvenFalse (oddCancel (oddCancel h))⟩
  · exact False.elim (hne rfl)
  · exact ⟨evenOddFalse (oddCancel (oddCancel (oddCancel h)))⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse h⟩
  · exact ⟨oddEvenFalse (oddCancel h)⟩
  · exact ⟨oddEvenFalse (oddCancel (oddCancel h))⟩
  · exact ⟨oddEvenFalse (oddCancel (oddCancel (oddCancel h)))⟩
  · exact False.elim (hne rfl)
theorem payloadCancel (i : Fin 6) (s t : OTerm alpha) (hi : 2 ≤ i.val)
    (h : Derivation body Delta (eqn (code i s) (code i t))) : Nonempty (Derivation body Delta (eqn s t)) := by
  fin_cases i
  · exact False.elim (by omega)
  · exact False.elim (by omega)
  · exact ⟨(evenCancel (oddCancel h))⟩
  · exact ⟨(evenCancel (oddCancel (oddCancel h)))⟩
  · exact ⟨(evenCancel (oddCancel (oddCancel (oddCancel h))))⟩
  · exact ⟨(oddCancel (oddCancel (oddCancel (oddCancel h))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.ArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.ArithmeticProof
