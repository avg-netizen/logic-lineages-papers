module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Original singleton certificate CODE is the actual iteration bound, not
list length. Initial history and final remaining lines are genuinely zero. -/
def InternalSingletonRun : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel
    (certificate I.ctag I.qtag raw)) (output I.ptag I.ctag I.atag raw))))
/-- Original rule1/tag2 add-zero arithmetic certificate. Actual unchanged CORE bound, initializer and finalizer. Only the internal
term-validity antecedent, never an external successful derivation. -/
def InternalCore : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
    (.add (RawAddZero.equalityValue I.ctag I.atag raw)
     (RawAddZero.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw)) (.succ .zero))))
/-- Actual literal Fuel wrapper, identical raw/index/fuel/certificate, including
zero fuel. No source/template selection, computation quotation or HB3 claim. -/
def InternalFuel : Prop := ∀ n (p : Program n) (logical old : Program 1) (x : Program 3)
 (I : Installation p logical old x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawAddZero.equalityValue I.ctag I.atag raw)
     (RawAddZero.equalityValue I.ctag I.atag raw))
    (certificate I.ctag I.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZeroCertificate.Targets
