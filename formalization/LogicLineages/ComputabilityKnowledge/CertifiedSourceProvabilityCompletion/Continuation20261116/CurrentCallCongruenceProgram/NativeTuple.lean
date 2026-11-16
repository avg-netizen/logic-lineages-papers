module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeTuple
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof HistoryRuleSuffix.NativeProof

theorem tailValues {arity n : Nat} (xs : List.Vector (Program arity) (n+1)) (xv : List.Vector (Term 0) (n+1)) (v : List.Vector Nat arity)
 (hx : ∀ i, evaluate (xs.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (xv.get i))) :
 ∀ i : Fin n, evaluate (xs.tail.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (xv.tail.get i)) := by
 intro i
 rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]
 exact hx i.succ

theorem value {arity n : Nat} (xs : List.Vector (Program arity) n) (v : List.Vector Nat arity) (xv : List.Vector (Term 0) n)
 (hx : ∀ i, evaluate (xs.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (xv.get i))) :
 evaluate (tupleCode xs) v = Encodable.encode (GorbowTermPrefixCode.encode (tupleTerm xv.toList)) := by
 induction n with
 | zero =>
  have hv : xv = nil := Subsingleton.elim _ _
  subst xv
  exact constantEval _ _ v
 | succ n ih =>
  have ht := ih xs.tail xv.tail (tailValues xs xv v hx)
  have hh : evaluate xs.head v = Encodable.encode (GorbowTermPrefixCode.encode xv.head) := by
   simpa only [List.Vector.get_zero] using hx 0
  have hp := NativePair.value xs.head (tupleCode xs.tail) v xv.head (tupleTerm xv.tail.toList) hh ht
  have hv : xv.toList = xv.head :: xv.tail.toList := congrArg List.Vector.toList (List.Vector.cons_head_tail xv).symm
  rw [hv]
  exact NativeScalar.unaryCode 2 _ v _ hp

theorem certificate {arity n : Nat} (xs ys codes : List.Vector (Program arity) n) (v : List.Vector Nat arity)
 (xv yv : List.Vector (Term 0) n) (cv : List.Vector Nat n)
 (hx : ∀ i, evaluate (xs.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (xv.get i)))
 (hy : ∀ i, evaluate (ys.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (yv.get i)))
 (hc : ∀ i, evaluate (codes.get i) v = cv.get i) :
 evaluate (tuple xs ys codes) v = tupleNumber xv yv cv := by
 induction n with
 | zero => exact CurrentRecursionStepProgram.NativeOperations.reflexivityEval _ v .zero (constantEval _ _ v)
 | succ n ih =>
  have hx0 : evaluate xs.head v = Encodable.encode (GorbowTermPrefixCode.encode xv.head) := by simpa only [List.Vector.get_zero] using hx 0
  have hy0 : evaluate ys.head v = Encodable.encode (GorbowTermPrefixCode.encode yv.head) := by simpa only [List.Vector.get_zero] using hy 0
  have hc0 : evaluate codes.head v = cv.head := by simpa only [List.Vector.get_zero] using hc 0
  have hct : ∀ i : Fin n, evaluate (codes.tail.get i) v = cv.tail.get i := by
   intro i
   rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]
   exact hc i.succ
  have hxt := value xs.tail v xv.tail (tailValues xs xv v hx)
  have hyt := value ys.tail v yv.tail (tailValues ys yv v hy)
  have ht := ih xs.tail ys.tail codes.tail xv.tail yv.tail cv.tail (tailValues xs xv v hx) (tailValues ys yv v hy) hct
  unfold tuple tupleNumber
  have hsimple := NativeScalar.simple false
   (pairCode xs.head (tupleCode xs.tail)) (pairCode ys.head (tupleCode ys.tail))
   (pair xs.head (tupleCode xs.tail) ys.head (tupleCode ys.tail) codes.head (tuple xs.tail ys.tail codes.tail))
   v (pairTerm xv.head (tupleTerm xv.tail.toList)) (pairTerm yv.head (tupleTerm yv.tail.toList))
   (NativePair.value _ _ v _ _ hx0 hxt) (NativePair.value _ _ v _ _ hy0 hyt)
  simp only [Bool.false_eq_true,ite_false,ite_true] at hsimple
  rw [hsimple]
  rw [NativePair.certificate _ _ _ _ _ _ v _ _ _ _ hx0 hxt hy0 hyt,hc0]
  exact congrArg (fun tailCode : Nat => unaryNumber (.succ (.var 0))
   (pairTerm xv.head (tupleTerm xv.tail.toList)) (pairTerm yv.head (tupleTerm yv.tail.toList))
   (pairNumber xv.head (tupleTerm xv.tail.toList) yv.head (tupleTerm yv.tail.toList) cv.head tailCode)) ht

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeTuple
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeTuple
