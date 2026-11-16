module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.TupleGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.CallGraph
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem constructor {arity inputs ctx n : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : Tags) (I : Installation p J) (tag : Program inputs) (tv : Term ctx)
 (xs ys codes : List.Vector (Program inputs) n) (xv yv cv : List.Vector (Term ctx) n)
 (htag : Computes p tag args tv)
 (hx : ∀ i, Computes p (xs.get i) args (xv.get i))
 (hy : ∀ i, Computes p (ys.get i) args (yv.get i))
 (hc : ∀ i, Computes p (codes.get i) args (cv.get i)) :
 Computes p (callConstructor tag xs ys codes) args (callCertificate J tv xv yv cv) := by
 have ht := LiteralRawMP.ConstructorSupportProof.unary p args LiteralNumeralPrefix.numeralCode J.numeralTag I.hn tag tv htag
 have hn : Computes p (HistoryRuleSuffix.constant inputs (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)))) args
  (rawNumeral (Term.numeral n)) := constantValue p args _
 have hxt := TupleGraph.value p args J I xs xv hx
 have hyt := TupleGraph.value p args J I ys yv hy
 have hct := TupleGraph.certificate p args J I xs ys codes xv yv cv hx hy hc
 have hp := BinaryGraph.pairGraph p args J I _ _ _ _ _ _ _ _ _ _ _ _ ht hxt ht hyt
  (GraphSupport.reflexivity p args J I _ _ ht) hct
 have htx := BinaryGraph.pairValueGraph p args J I _ _ _ _ ht hxt
 have hty := BinaryGraph.pairValueGraph p args J I _ _ _ _ ht hyt
 have hh := BinaryGraph.pairGraph p args J I _ _ _ _ _ _ _ _ _ _ _ _ hn htx hn hty
  (GraphSupport.reflexivity p args J I _ _ hn) hp
 exact UnaryGraph.closed p args J I (.universalFunction (.var 0)) _ _ _ _ _ _
  (BinaryGraph.pairValueGraph p args J I _ _ _ _ hn htx)
  (BinaryGraph.pairValueGraph p args J I _ _ _ _ hn hty) hh

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.CallGraph
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.CallGraph
