module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Literal finite twelve-node package. Every program AST is fixed before tags
are selected, and before any runtime input/index/fuel. No tag occurs in an AST. -/
def items (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : List Packed :=
 [⟨1,FullFormulaInstantiation.line f⟩,
  ⟨2,HistoryCodec.pair⟩, ⟨2,HistoryCodec.cons⟩, ⟨2,HistoryAppend.append⟩,
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩, ⟨1,LiteralSyntaxValidator.lineValidator⟩,
  ⟨1,FullFormulaInstantiation.logicalLeaf f old⟩,
  ⟨4,FullFormulaInstantiationDispatcher.dispatcher f old arithmetic x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (FullFormulaInstantiationCertificate.kernel f old arithmetic x)⟩,
  ⟨5,FullFormulaInstantiationCertificate.checker f old arithmetic x⟩,
  ⟨5,FullFormulaInstantiationCertificate.verifier f old arithmetic x⟩]
def carrier (f : Formula 1) (old arithmetic : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items f old arithmetic x)
/-- Same concrete chosen registry witnesses for all runtime inputs. No source
Theory(carrier) inclusion into a different published root is asserted. -/
def RuntimeCapability (f : Formula 1) (old arithmetic : Program 1) (x : Program 3)
 (I : FullFormulaInstantiationCertificate.Installation (carrier f old arithmetic x) f old arithmetic x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (carrier f old arithmetic x))
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.itag I.ptag index fuel
      (FullFormulaInstantiationCertificate.certificate I.ctag I.qtag raw))
     (FullFormulaInstantiationCertificate.output f I.ptag I.ctag I.atag raw))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
       (.add (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)
        (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw))
       (FullFormulaInstantiationCertificate.certificate I.ctag I.qtag raw)) (.succ .zero))
     (SixSol20261112.Fuel.success I.utag index fuel .zero
      (.add (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw)
       (FullFormulaInstantiation.formulaValue I.ctag I.atag f raw))
      (FullFormulaInstantiationCertificate.certificate I.ctag I.qtag raw))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationRegistry
