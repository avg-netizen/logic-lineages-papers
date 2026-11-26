module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Original singleton certificate CODE is the actual iteration bound, not
list length. Initial history and final remaining lines are genuinely zero. -/
def InternalSingletonRun : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (raw rawB rawV index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag raw)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawB)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawV)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.pairTag index fuel
    (certificate I.consTag I.qtag raw rawB rawV)) (output I.pairTag I.consTag I.appendTag raw rawB rawV))))))
/-- Original rule0/tag12 equality-replacement logical certificate. Actual unchanged CORE bound, initializer and finalizer. Only the internal
term-validity antecedent, never an external successful derivation. -/
def InternalCore : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (raw rawB rawV index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag raw)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawB)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawV)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
    (.add (RawAddRightReplace.formulaValue I.consTag I.appendTag raw rawB rawV)
     (RawAddRightReplace.formulaValue I.consTag I.appendTag raw rawB rawV))
    (certificate I.consTag I.qtag raw rawB rawV)) (.succ .zero))))))
/-- Actual literal Fuel wrapper, identical raw/index/fuel/certificate, including
zero fuel. No source/template selection, computation quotation or HB3 claim. -/
def InternalFuel : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p old arithmetic x), ∀ ctx (raw rawB rawV index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag raw)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawB)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag rawV)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawAddRightReplace.formulaValue I.consTag I.appendTag raw rawB rawV)
     (RawAddRightReplace.formulaValue I.consTag I.appendTag raw rawB rawV))
    (certificate I.consTag I.qtag raw rawB rawV))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightCertificate.Targets
