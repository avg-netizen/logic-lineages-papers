module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Original multiplication prefix grammar, independently of arithmetic truth. -/
def InternalMultiplicationValidity : Prop := ∀ n (p : Program n) (vtag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (t u : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag t)
   (.imp (RawReflexivityDispatcher.valid vtag u)
    (RawReflexivityDispatcher.valid vtag (mulRaw ctag atag t u)))))
/-- Actual original mul-zero certificate at the common arithmetic checker. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
    (mulRaw I.ctag I.atag t (RawAdditionComputation.zeroRaw I.ctag))
    (RawAdditionComputation.zeroRaw I.ctag)
    (RawMultiplicationCertificates.ZeroCertificate.certificate I.ctag I.mulZeroTag t))))
/-- Genuine multiplication computation step for an arbitrary raw right operand.
Input product=num(z) is transported through the actual addition evaluator and
arbitrary-count congruence to product(next)=num(z+m). No step-success premise. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (m u z cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag u)
   (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
     (mulRaw I.ctag I.atag (LiteralNumeralPrefix.numeralCall I.numeralTag m) u)
     (LiteralNumeralPrefix.numeralCall I.numeralTag z) cert)
    (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
     (mulRaw I.ctag I.atag (LiteralNumeralPrefix.numeralCall I.numeralTag m)
      (RawAdditionComputation.succRaw I.ctag u))
     (LiteralNumeralPrefix.numeralCall I.numeralTag (.add z m))
     (stepCertificate I.mpTag I.qtag I.reflexivityTag I.mulSuccTag I.iteratorTag
      I.congruenceIteratorTag I.numeralTag I.prefixTag I.ptag I.ctag I.atag I.rightTag m u z cert)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationComputation.Targets
