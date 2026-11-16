module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.BinaryGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TupleGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem tailComputes {arity inputs ctx n : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (xs : List.Vector (Program inputs) (n+1)) (xv : List.Vector (Term ctx) (n+1))
 (hx : ∀ i, Computes p (xs.get i) args (xv.get i)) :
 ∀ i : Fin n, Computes p (xs.tail.get i) args (xv.tail.get i) := by
 intro i
 rw [List.Vector.get_tail_succ,List.Vector.get_tail_succ]
 exact hx i.succ

theorem value {arity inputs ctx n : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (xs : List.Vector (Program inputs) n) (xv : List.Vector (Term ctx) n)
 (hx : ∀ i, Computes p (xs.get i) args (xv.get i)) :
 Computes p (tupleCode xs) args (tupleValue J xv.toList) := by
 induction n with
 | zero =>
  have hv : xv = nil := Subsingleton.elim _ _
  subst xv
  exact constantValue p args _
 | succ n ih =>
  have ht := ih xs.tail xv.tail (tailComputes p args xs xv hx)
  have hh : Computes p xs.head args xv.head := by simpa only [List.Vector.get_zero] using hx 0
  have hp := BinaryGraph.pairValueGraph p args J I xs.head (tupleCode xs.tail) xv.head (tupleValue J xv.tail.toList) hh ht
  have hv : xv.toList = xv.head :: xv.tail.toList := by
   exact congrArg List.Vector.toList (List.Vector.cons_head_tail xv).symm
  rw [hv]
  exact GraphSupport.unaryCode p args J I 2 _ _ hp

theorem certificate {arity inputs ctx n : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (xs ys codes : List.Vector (Program inputs) n) (xv yv cv : List.Vector (Term ctx) n)
 (hx : ∀ i, Computes p (xs.get i) args (xv.get i))
 (hy : ∀ i, Computes p (ys.get i) args (yv.get i))
 (hc : ∀ i, Computes p (codes.get i) args (cv.get i)) :
 Computes p (tuple xs ys codes) args (tupleCertificate J xv yv cv) := by
 induction n with
 | zero => exact GraphSupport.reflexivity p args J I _ _ (constantValue p args _)
 | succ n ih =>
  have hx0 : Computes p xs.head args xv.head := by simpa only [List.Vector.get_zero] using hx 0
  have hy0 : Computes p ys.head args yv.head := by simpa only [List.Vector.get_zero] using hy 0
  have hc0 : Computes p codes.head args cv.head := by simpa only [List.Vector.get_zero] using hc 0
  have hxt := value p args J I xs.tail xv.tail (tailComputes p args xs xv hx)
  have hyt := value p args J I ys.tail yv.tail (tailComputes p args ys yv hy)
  have hct := ih xs.tail ys.tail codes.tail xv.tail yv.tail cv.tail
   (tailComputes p args xs xv hx) (tailComputes p args ys yv hy) (tailComputes p args codes cv hc)
  exact UnaryGraph.closed p args J I (.succ (.var 0)) _ _ _ _ _ _
   (BinaryGraph.pairValueGraph p args J I _ _ _ _ hx0 hxt)
   (BinaryGraph.pairValueGraph p args J I _ _ _ _ hy0 hyt)
   (BinaryGraph.pairGraph p args J I _ _ _ _ _ _ _ _ _ _ _ _ hx0 hxt hy0 hyt hc0 hct)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TupleGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TupleGraph
