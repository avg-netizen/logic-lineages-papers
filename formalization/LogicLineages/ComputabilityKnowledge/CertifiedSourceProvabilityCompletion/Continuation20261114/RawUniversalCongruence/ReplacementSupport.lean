module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ReflexivityProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ReplacementSupport
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
structure CoreInstallation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 RawUniversalReplaceDispatcher.Installation p old a x where
 itag : Nat
 qctag : Nat
 hi : (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (RawUniversalReplaceCertificate.kernel old a x)⟩
 hqc : (nodes p)[qctag]? = some ⟨5,RawUniversalReplaceCertificate.checker old a x⟩
def InternalSingletonRun : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : CoreInstallation p old arithmetic x), ∀ ctx (raw rawB index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.imp (RawReflexivityDispatcher.valid I.vtag rawB)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel
    (RawUniversalReplaceCertificate.certificate I.ctag I.qtag raw rawB)) (RawUniversalReplaceCertificate.output I.ptag I.ctag I.atag raw rawB)))))
/-- Original rule0/tag12 equality-replacement logical certificate. Actual unchanged CORE bound, initializer and finalizer. Only the internal
term-validity antecedent, never an external successful derivation. -/
def InternalCore : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : CoreInstallation p old arithmetic x), ∀ ctx (raw rawB index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.imp (RawReflexivityDispatcher.valid I.vtag rawB)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
    (.add (RawUniversalReplace.formulaValue I.ctag I.atag raw rawB)
     (RawUniversalReplace.formulaValue I.ctag I.atag raw rawB))
    (RawUniversalReplaceCertificate.certificate I.ctag I.qtag raw rawB)) (.succ .zero)))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.ReplacementSupport
