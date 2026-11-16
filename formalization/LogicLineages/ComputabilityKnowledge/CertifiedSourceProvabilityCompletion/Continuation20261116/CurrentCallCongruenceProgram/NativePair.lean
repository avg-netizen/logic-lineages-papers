module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeBinary
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof HistoryRuleSuffix.NativeProof

theorem value {arity : Nat} (a b : Program arity) (v : List.Vector Nat arity) (av bv : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode av))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode bv)) :
 evaluate (pairCode a b) v = Encodable.encode (GorbowTermPrefixCode.encode (pairTerm av bv)) := by
 have hs := NativeScalar.operation false a b v av bv ha hb
 exact NativeScalar.operation false _ a v _ av (NativeScalar.operation true _ _ v _ _ hs hs) ha

theorem certificate {arity : Nat} (a b c d hac hbd : Program arity) (v : List.Vector Nat arity)
 (av bv cv dv : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode av))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode bv))
 (hc : evaluate c v = Encodable.encode (GorbowTermPrefixCode.encode cv))
 (hd : evaluate d v = Encodable.encode (GorbowTermPrefixCode.encode dv)) :
 evaluate (pair a b c d hac hbd) v = pairNumber av bv cv dv (evaluate hac v) (evaluate hbd v) := by
 have hs := NativeBinary.binaryEval false a b c d hac hbd v av bv cv dv ha hb hc hd
 have hab := NativeScalar.operation false a b v av bv ha hb
 have hcd := NativeScalar.operation false c d v cv dv hc hd
 have hm := NativeBinary.binaryEval true _ _ _ _ _ _ v _ _ _ _ hab hab hcd hcd
 unfold pair
 rw [NativeBinary.binaryEval false _ a _ c _ hac v _ av _ cv
  (NativeScalar.operation true _ _ v _ _ hab hab) ha (NativeScalar.operation true _ _ v _ _ hcd hcd) hc]
 rw [hm,hs]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
