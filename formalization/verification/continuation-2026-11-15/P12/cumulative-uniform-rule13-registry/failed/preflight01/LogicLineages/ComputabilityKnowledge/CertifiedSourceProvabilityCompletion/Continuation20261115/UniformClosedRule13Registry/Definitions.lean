module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Certificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.BundleProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Literal26 ASTs, all fixed before tags and all runtime inputs. No selected
registry tag is embedded in an AST, and no self-source tuple is selected here. -/
def items (old arithmetic : Program 1) (x : Program 3) : List Packed :=
 [⟨1,UniformClosedCase13.caseCode⟩,
  ⟨1,HistoryCodec.predecessor⟩,
  ⟨2,UniformClosedInstanceRecognizer.instanceCode⟩,
  ⟨3,UniformClosedSubstitutionRawFold.foldCode⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩,
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩,
  ⟨2,HistoryCodec.pair⟩,
  ⟨2,HistoryCodec.cons⟩,
  ⟨1,HistoryDecoder.decoder true⟩,
  ⟨1,HistoryLengthOffset.lengthProgram⟩,
  ⟨1,HistoryLookup.head⟩,
  ⟨1,HistoryLookup.tail⟩,
  ⟨2,HistoryAppend.append⟩,
  ⟨3,UniformClosedSubstitutionEmit.emitCode⟩,
  ⟨2,LiteralSyntaxStep.stepCode⟩,
  ⟨2,LiteralSyntaxScan.scanCode⟩,
  ⟨2,HistoryCodec.difference⟩,
  ⟨2,HistoryLookup.lookup⟩,
  ⟨1,HistoryDecoder.decoder false⟩,
  ⟨2,UniformClosedRule13.lineConstructor⟩,
  ⟨1,LiteralSyntaxValidator.lineValidator⟩,
  ⟨1,UniformClosedRule13.logicalLeaf old⟩,
  ⟨4,UniformClosedRule13Dispatcher.dispatcher old arithmetic x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (UniformClosedRule13Certificate.kernel old arithmetic x)⟩,
  ⟨5,UniformClosedRule13Certificate.checker old arithmetic x⟩,
  ⟨5,UniformClosedRule13Certificate.verifier old arithmetic x⟩]
def carrier (old arithmetic : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items old arithmetic x)
/-- Parametric in the ACTUAL root, enabling later reconstruction of global tags;
no inclusion or retagging from Theory(carrier) into another root is asserted. -/
def RuntimeCapability {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) : Prop :=
 ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.caseTag I.predTag I.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag formula replacement
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (UniformClosedRule13Certificate.output I.ptag I.ctag I.caseTag I.predTag formula replacement))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry
