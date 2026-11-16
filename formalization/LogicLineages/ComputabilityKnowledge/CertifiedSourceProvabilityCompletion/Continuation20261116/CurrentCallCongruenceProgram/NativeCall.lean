module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeTuple
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeCall
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof HistoryRuleSuffix.NativeProof

theorem certificate {arity n : Nat} (tag : Program arity) (xs ys codes : List.Vector (Program arity) n)
 (v : List.Vector Nat arity) (target : Nat) (xv yv : List.Vector (Term 0) n) (cv : List.Vector Nat n)
 (htag : evaluate tag v = target)
 (hx : ∀ i, evaluate (xs.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (xv.get i)))
 (hy : ∀ i, evaluate (ys.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (yv.get i)))
 (hc : ∀ i, evaluate (codes.get i) v = cv.get i) :
 evaluate (callConstructor tag xs ys codes) v = callNumber target xv yv cv := by
 have ht : evaluate (HistoryRuleSuffix.applyOne LiteralNumeralPrefix.numeralCode tag) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral target : Term 0)) := by
  rw [oneEval,htag,LiteralNumeralPrefix.StatementChecks.exactNative]
 have hn : evaluate (HistoryRuleSuffix.constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)))) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)) := constantEval _ _ v
 have hxt := NativeTuple.value xs v xv hx
 have hyt := NativeTuple.value ys v yv hy
 have hct := NativeTuple.certificate xs ys codes v xv yv cv hx hy hc
 have htx := NativePair.value _ _ v _ _ ht hxt
 have hty := NativePair.value _ _ v _ _ ht hyt
 have hp := NativePair.certificate _ _ _ _ _ _ v _ _ _ _ ht hxt ht hyt
 have hh := NativePair.certificate _ _ _ _ _ _ v _ _ _ _ hn htx hn hty
 unfold callConstructor
 rw [NativeScalar.simple true _ _ _ v _ _ (NativePair.value _ _ v _ _ hn htx) (NativePair.value _ _ v _ _ hn hty)]
 rw [hh,hp,hct,CurrentRecursionStepProgram.NativeOperations.reflexivityEval _ v _ ht,
  CurrentRecursionStepProgram.NativeOperations.reflexivityEval _ v _ hn]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeCall
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeCall
