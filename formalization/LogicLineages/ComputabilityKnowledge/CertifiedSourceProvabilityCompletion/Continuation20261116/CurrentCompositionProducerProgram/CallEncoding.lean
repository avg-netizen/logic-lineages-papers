module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open CurrentCallCongruenceProgram
open CurrentRecursionBaseProgram.NativePrimitives HistoryRuleSuffix.NativeProof
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem native {arity n : Nat} (tag : Program arity) (raw : List.Vector (Program arity) n)
 (v : List.Vector Nat arity) (target : Nat) (terms : List.Vector (Term 0) n)
 (htag : evaluate tag v = target)
 (hraw : ∀ i, evaluate (raw.get i) v = Encodable.encode (GorbowTermPrefixCode.encode (terms.get i))) :
 evaluate (callCode tag raw) v = Encodable.encode (GorbowTermPrefixCode.encode (call target terms)) := by
 have ht : evaluate (applyOne LiteralNumeralPrefix.numeralCode tag) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral target : Term 0)) := by
  rw [oneEval,htag,LiteralNumeralPrefix.StatementChecks.exactNative]
 have hn : evaluate (constant arity (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)))) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)) := constantEval _ _ v
 have hx := NativeTuple.value raw v terms hraw
 exact NativeScalar.unaryCode 5 _ v _ (NativePair.value _ _ v _ _ hn (NativePair.value _ _ v _ _ ht hx))

theorem graph {arity inputs n ctx : Nat} (p : Program arity) (args : List.Vector (Term ctx) inputs)
 (J : CurrentCallCongruenceProgram.Tags) (I : CurrentCallCongruenceProgram.Installation p J)
 (tag : Program inputs) (raw : List.Vector (Program inputs) n) (target : Term ctx) (terms : List.Vector (Term ctx) n)
 (htag : Computes p tag args target) (hraw : ∀ i, Computes p (raw.get i) args (terms.get i)) :
 Computes p (callCode tag raw) args (callValue J target terms) := by
 have ht := LiteralRawMP.ConstructorSupportProof.unary p args LiteralNumeralPrefix.numeralCode J.numeralTag I.hn tag target htag
 have hn : Computes p (constant inputs (Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral n : Term 0)))) args
  (rawNumeral (Term.numeral n)) := constantValue p args _
 have hx := TupleGraph.value p args J I raw terms hraw
 exact GraphSupport.unaryCode p args J I 5 _ _
  (BinaryGraph.pairValueGraph p args J I _ _ _ _ hn (BinaryGraph.pairValueGraph p args J I _ _ _ _ ht hx))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
