module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual internal preservation of the original rule1/tag2 addZero line
through the OUTER rule1/tag3 recognizer. The outer recognition failure must
be derived internally from the original encoding, not native calibration.
The lower installed arithmetic AST is not an extra acceptance assumption. -/
def InternalAddZero : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,RawAddZero.lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,arithmetic old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (RawAddZero.lineCall qtag raw)) (.succ .zero))))
/-- Actual original dispatcher: rule1 is selected only AFTER the failed rule0
test. All runtime index/fuel/history/raw values remain arbitrary. Only genuine
internal term-validity is an antecedent; no successful rule/dispatcher premise. -/
def InternalDispatcher : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (raw index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
    (RawAddZero.lineCall I.qtag raw)) (.succ .zero))))
/-- Original singleton certificate CODE is the actual iteration bound, not
list length. Initial history and final remaining lines are genuinely zero. -/
def InternalSingletonRun : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : CertificateInstallation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel
    (certificate I.ctag I.qtag raw)) (output I.ptag I.ctag I.atag raw))))
/-- Original rule1/tag2 add-zero arithmetic certificate. Actual unchanged CORE bound, initializer and finalizer. Only the internal
term-validity antecedent, never an external successful derivation. -/
def InternalCore : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : CertificateInstallation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
    (.add (RawAddZero.equalityValue I.ctag I.atag raw)
     (RawAddZero.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw)) (.succ .zero))))
/-- Actual literal Fuel wrapper, identical raw/index/fuel/certificate, including
zero fuel. No source/template selection, computation quotation or HB3 claim. -/
def InternalFuel : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : CertificateInstallation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawAddZero.equalityValue I.ctag I.atag raw)
     (RawAddZero.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.Targets
