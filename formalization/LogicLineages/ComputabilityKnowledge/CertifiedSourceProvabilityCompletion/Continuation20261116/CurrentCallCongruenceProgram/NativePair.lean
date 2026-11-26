module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeBinary
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
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
 let ab := FixedFormulaSubstitution.binary 3 a b
 let cd := FixedFormulaSubstitution.binary 3 c d
 let hsCode := CurrentCallCongruenceProgram.binary false a b c d hac hbd
 have hm := NativeBinary.binaryEval true ab ab cd cd hsCode hsCode v
  (.add av bv) (.add av bv) (.add cv dv) (.add cv dv) hab hab hcd hcd
 let hmCode := CurrentCallCongruenceProgram.binary true ab ab cd cd hsCode hsCode
 have hmulAB : evaluate (FixedFormulaSubstitution.binary 4 ab ab) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.mul (.add av bv) (.add av bv))) :=
  NativeScalar.operation true ab ab v _ _ hab hab
 have hmulCD : evaluate (FixedFormulaSubstitution.binary 4 cd cd) v =
  Encodable.encode (GorbowTermPrefixCode.encode (Term.mul (.add cv dv) (.add cv dv))) :=
  NativeScalar.operation true cd cd v _ _ hcd hcd
 have hout := NativeBinary.binaryEval false (FixedFormulaSubstitution.binary 4 ab ab) a
  (FixedFormulaSubstitution.binary 4 cd cd) c hmCode hac v
  (.mul (.add av bv) (.add av bv)) av (.mul (.add cv dv) (.add cv dv)) cv hmulAB ha hmulCD hc
 change evaluate (CurrentCallCongruenceProgram.binary false (FixedFormulaSubstitution.binary 4 ab ab) a
  (FixedFormulaSubstitution.binary 4 cd cd) c hmCode hac) v = _
 rw [hout]
 change binaryNumber false (.mul (.add av bv) (.add av bv)) av (.mul (.add cv dv) (.add cv dv)) cv
  (evaluate (CurrentCallCongruenceProgram.binary true ab ab cd cd hsCode hsCode) v) (evaluate hac v) = _
 rw [hm]
 change binaryNumber false (.mul (.add av bv) (.add av bv)) av (.mul (.add cv dv) (.add cv dv)) cv
  (binaryNumber true (.add av bv) (.add av bv) (.add cv dv) (.add cv dv)
   (evaluate (CurrentCallCongruenceProgram.binary false a b c d hac hbd) v)
   (evaluate (CurrentCallCongruenceProgram.binary false a b c d hac hbd) v)) (evaluate hac v) = _
 rw [hs]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativePair
