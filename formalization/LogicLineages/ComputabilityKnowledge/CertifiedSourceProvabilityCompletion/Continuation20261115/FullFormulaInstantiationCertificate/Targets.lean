module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.Targets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual original encoded certificate CODE bound, initial empty history,
final empty lines; runtime fuel may be zero. -/
def InternalSingletonRun : Prop := ∀ (f : Formula 1) n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p f old arithmetic x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.vtag raw)
  (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel (certificate I.ctag I.qtag raw))
   (output f I.ptag I.ctag I.atag raw))))
/-- Original fixed-template tag13 [phi,u] singleton under unchanged CORE. -/
def InternalCore : Prop := ∀ (f : Formula 1) n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p f old arithmetic x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)
    (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw))
   (certificate I.ctag I.qtag raw)) (.succ .zero))))
/-- Literal Fuel at the same index/fuel/code, including zero; no full source or HB3 claim. -/
def InternalFuel : Prop := ∀ (f : Formula 1) n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : Installation p f old arithmetic x), ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.vtag raw)
  (SixSol20261112.Fuel.success I.utag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)
    (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw))
   (certificate I.ctag I.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.Targets
