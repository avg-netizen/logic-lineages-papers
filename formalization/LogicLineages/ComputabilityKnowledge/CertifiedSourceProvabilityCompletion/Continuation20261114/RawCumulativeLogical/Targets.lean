module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Genuine internal preservation of reflexivity through the outer logical
replacement refinement. Both selector branch outputs are proved one; native
calibration is not reflected into a proof. -/
def InternalReflexivity : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,RawReflexivity.lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,logical old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (RawReflexivity.lineCall qtag raw)) (.succ .zero))))
def InternalDispatcher : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (raw index fuel history : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
    (RawReflexivity.lineCall I.qtag raw)) (.succ .zero))))
/-- Original singleton certificate CODE is the actual iteration bound, not
list length. Initial history and final remaining lines are genuinely zero. -/
def InternalSingletonRun : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : CertificateInstallation p old a x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel
    (certificate I.ctag I.qtag raw)) (output I.ptag I.ctag I.atag raw))))
/-- Actual unchanged CORE bound, initializer and finalizer. Only the internal
term-validity antecedent, never an external successful derivation. -/
def InternalCore : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : CertificateInstallation p old a x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag raw)
     (RawReflexivity.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw)) (.succ .zero))))
/-- Actual literal Fuel wrapper, identical raw/index/fuel/certificate, including
zero fuel. No source/template selection, computation quotation or HB3 claim. -/
def InternalFuel : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : CertificateInstallation p old a x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag raw)
     (RawReflexivity.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeLogical.Targets
