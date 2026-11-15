module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule13Registry.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Base leaf BEFORE uniform Rule13; avoids accidental double extension. -/
abbrev previousLogical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 CumulativeUniformRule13Registry.previousLogical f lhs rhs old
/-- Concrete current26AST list, fixed before root/tags/runtime inputs. -/
def currentItems (old arithmetic : Program 1) (x : Program 3) : List Packed :=
 [⟨1,UniformClosedCase12.caseCode⟩,
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
  ⟨3,UniformClosedRule12.lineConstructor⟩,
  ⟨1,LiteralSyntaxValidator.lineValidator⟩,
  ⟨1,UniformClosedRule12.logicalLeaf old⟩,
  ⟨4,UniformClosedRule12Dispatcher.dispatcher old arithmetic x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (UniformClosedRule12Certificate.kernel old arithmetic x)⟩,
  ⟨5,UniformClosedRule12Certificate.checker old arithmetic x⟩,
  ⟨5,UniformClosedRule12Certificate.verifier old arithmetic x⟩]
def items {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : List Packed :=
 CumulativeUniformRule13Registry.items f lhs rhs t old a x ++
 currentItems (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
def carrier {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle (items f lhs rhs t old a x)
structure JointInstallation {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) where
 previous : CumulativeUniformRule13Registry.JointInstallation p f lhs rhs t old a x
 current : UniformClosedRule12Certificate.Installation p (previousLogical f lhs rhs old) (RawMulNewestAddition.arithmetic a) x
def CompilerCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.previous.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.coreTag I.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.previous.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.previous.previous.template.certificateTag values))))
def EqualityCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.previous.previous.current.ctag I.previous.previous.previous.current.qtag raw)) (.succ .zero))))
def FullFormulaCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.previous.previous.current.ctag I.previous.previous.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.previous.previous.current.ctag I.previous.previous.current.qtag raw)) (.succ .zero))))
def RetentionCapability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.coreTag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel context formula code) (.succ .zero))))
def Uniform13Capability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.previous.current.caseTag I.previous.current.predTag I.previous.current.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag formula replacement
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.previous.current.fval I.previous.current.vtag formula replacement)
   (.conj (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add C C) code) (.succ .zero))
    (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add C C) code))))
def Uniform12Capability {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) (I : JointInstallation p f lhs rhs t old a x) : Prop :=
 ∀ ctx (formula left right index fuel : Term ctx),
 let C := UniformClosedRule12.conclusionValue I.current.caseTag I.current.predTag I.current.ctag formula left right
 let code := UniformClosedRule12Certificate.certificate I.current.ctag I.current.constructorTag formula left right
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.current.fval I.current.vtag formula left right)
   (.conj (.equal (LiteralCheckerAcceptance.runCall I.current.iteratorTag I.current.ptag index fuel code)
      (UniformClosedRule12Certificate.output I.current.ptag I.current.ctag I.current.caseTag I.current.predTag formula left right))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall I.current.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.current.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Registry
