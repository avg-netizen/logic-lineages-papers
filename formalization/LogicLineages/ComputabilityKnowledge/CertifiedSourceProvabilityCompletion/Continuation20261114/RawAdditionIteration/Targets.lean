module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
/-- Exact constructor equations, no validity or successful checking assumptions. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (unaryCall I.baseTag t) (RawIteratedSucc.state I.ptag (RawAdditionComputation.zeroRaw I.ctag) t
   (RawCumulativeArithmetic.certificate I.ctag I.zeroTag t))))
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v cert : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (binaryCall I.stepTag t (RawIteratedSucc.state I.ptag u v cert))
   (RawIteratedSucc.state I.ptag (RawAdditionComputation.succRaw I.ctag u) (RawAdditionComputation.succRaw I.ctag v)
    (RawAdditionComputation.stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag t u v cert))))
/-- Actual arbitrary-count computation: concrete numeral and result syntax,
with the certificate extracted from the same PR iterator. No step-success premise. -/
def InternalIteration : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (count t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.conj (.equal (RawIteratedSucc.first I.leftTag (binaryCall I.iteratorTag count t))
     (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
    (.conj (.equal (RawIteratedSucc.second I.leftTag I.rightTag (binaryCall I.iteratorTag count t))
      (binaryCall I.prefixTag count t))
     (.conj (RawReflexivityDispatcher.valid I.vtag (binaryCall I.prefixTag count t))
      (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
       (RawAdditionComputation.addRaw I.ctag I.atag t (SixSol20261113.LiteralNumeralPrefix.numeralCall I.numeralTag count))
       (binaryCall I.prefixTag count t)
       (RawIteratedSucc.third I.rightTag (binaryCall I.iteratorTag count t))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionIteration.Targets
