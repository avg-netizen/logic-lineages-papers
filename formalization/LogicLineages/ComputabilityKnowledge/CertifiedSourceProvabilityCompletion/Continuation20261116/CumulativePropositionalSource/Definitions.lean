module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
abbrev previousLogical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 CumulativeUniformRule12Source.logical f lhs rhs old
abbrev logical (f : Formula 1) (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 UniformClosedPropositional.logicalLeaf (previousLogical f lhs rhs old)
abbrev arithmetic (a : Program 1) : Program 1 := RawMulNewestAddition.arithmetic a
abbrev verifier (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) : Program 5 :=
 UniformClosedPropositionalCertificate.verifier (previousLogical f lhs rhs old)
  (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (f : Formula 1) (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier f lhs rhs old a baseX)) pR
/-- Exact constructor and auxiliary ASTs, all fixed before tags or source tuple. -/
def currentItems (old ar : Program 1) (x : Program 3) : List Packed :=
 [⟨3,UniformClosedPropositional.lineConstructor false⟩,
  ⟨3,UniformClosedPropositional.lineConstructor true⟩,
  ⟨2,HistoryCodec.pair⟩,⟨2,HistoryCodec.cons⟩,⟨2,HistoryAppend.append⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩,⟨2,LiteralSyntaxScan.scanCode⟩,
  ⟨1,LiteralSyntaxValidator.lineValidator⟩,⟨1,UniformClosedPropositional.logicalLeaf old⟩,
  ⟨4,UniformClosedPropositionalCertificate.dispatcher old ar x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (UniformClosedPropositionalCertificate.kernel old ar x)⟩,
  ⟨5,UniformClosedPropositionalCertificate.checker old ar x⟩,
  ⟨5,UniformClosedPropositionalCertificate.verifier old ar x⟩]
def items {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : List Packed :=
 CumulativeUniformRule12Registry.items f lhs rhs t old a x ++
 currentItems (previousLogical f lhs rhs old) (arithmetic a) x
def carrier {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) : Program 6 := ReflexivityInstalled.bundle (items f lhs rhs t old a x)
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,carrier f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩]
structure JointInstallation {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (x : Program 3) where
 previous : CumulativeUniformRule12Registry.JointInstallation p f lhs rhs t old a x
 currentK : UniformClosedPropositionalCertificate.Installation p (previousLogical f lhs rhs old) (arithmetic a) x false
 currentS : UniformClosedPropositionalCertificate.Installation p (previousLogical f lhs rhs old) (arithmetic a) x true
def Packages (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := logical f lhs rhs old
 let ar := arithmetic a
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l ar x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l ar x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l ar x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l ar baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l ar baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l ar baseX pF pR c
/-- Exact reinstalled interface in this same newly selected source S. -/
def CompilerCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.conj (RawReflexivityDispatcher.valid I.previous.previous.previous.previous.previous.validatorTag (GorbowPRDefiningEquations.call I.previous.previous.previous.previous.template.quoteTag values))
  (RawEqualityComposition.accepted I.currentK.coreTag I.previous.previous.previous.previous.previous.consTag I.previous.previous.previous.previous.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.previous.previous.previous.previous.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.previous.previous.previous.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.previous.previous.previous.previous.template.certificateTag values))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def EqualityCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.previous.previous.previous.previous.current.ctag I.previous.previous.previous.previous.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.previous.previous.previous.previous.current.ctag I.previous.previous.previous.previous.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.previous.previous.previous.previous.current.ctag I.previous.previous.previous.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def FullFormulaCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (RawReflexivityDispatcher.valid I.previous.previous.previous.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero
   (.add (FullFormulaInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag f raw)
    (FullFormulaInstantiation.formulaValue I.previous.previous.previous.current.ctag I.previous.previous.previous.current.atag f raw))
   (FullFormulaInstantiationCertificate.certificate I.previous.previous.previous.current.ctag I.previous.previous.previous.current.qtag raw)) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def RetentionCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.current.coreTag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel context formula code) (.succ .zero))))
/-- Original prior retention capability, also reinstalled at new CORE. -/
def PriorRetentionCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (index fuel context formula code : Term ctx), Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
 (.imp (.equal (LiteralCheckerAcceptance.coreCall I.previous.previous.current.coreTag index fuel context formula code) (.succ .zero))
       (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel context formula code) (.succ .zero))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def Uniform13Capability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (formula replacement index fuel : Term ctx),
 let C := UniformClosedRule13.conclusionValue I.previous.previous.current.caseTag I.previous.previous.current.predTag I.previous.previous.current.ctag formula replacement
 let code := UniformClosedRule13Certificate.certificate I.previous.previous.current.ctag I.previous.previous.current.constructorTag formula replacement
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
  (.imp (UniformClosedInstanceRecognizer.guards I.previous.previous.current.fval I.previous.previous.current.vtag formula replacement)
   (.conj (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add C C) code) (.succ .zero))
    (SixSol20261112.Fuel.success I.currentK.verifierTag index fuel .zero (.add C C) code))))
/-- Exact reinstalled interface in this same newly selected source S. -/
def Uniform12Capability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX)
  f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ ctx (formula left right index fuel : Term ctx),
 let C := UniformClosedRule12.conclusionValue I.previous.current.caseTag I.previous.current.predTag I.previous.current.ctag formula left right
 let code := UniformClosedRule12Certificate.certificate I.previous.current.ctag I.previous.current.constructorTag formula left right
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
  (.imp (UniformClosedRule12.guards I.previous.current.fval I.previous.current.vtag formula left right)
   (.conj (.equal (LiteralCheckerAcceptance.runCall I.currentK.iteratorTag I.previous.current.ptag index fuel code)
      (UniformClosedRule12Certificate.output I.previous.current.ptag I.previous.current.ctag I.previous.current.caseTag I.previous.current.predTag formula left right))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.currentK.verifierTag index fuel .zero (.add C C) code)))))
/-- Both original singleton recipes in the one new source; K/S may use
separate constructor tags, while shared checker/verifier identities are explicit. -/
def PropositionalCapability {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1)
 (I : JointInstallation (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) : Prop :=
 ∀ isS ctx (rawA rawB rawC index fuel : Term ctx),
 let J : UniformClosedPropositionalCertificate.Installation (root f lhs rhs pF pR old a baseX)
  (previousLogical f lhs rhs old) (arithmetic a) (SaturatedAxiomLeaf.saturated baseX) isS :=
  Bool.rec I.currentK I.currentS isS
 let C := UniformClosedPropositional.conclusionValue isS J.ctag J.atag rawA rawB rawC
 let code := UniformClosedPropositionalCertificate.certificate J.ctag J.constructorTag rawA rawB rawC
 Nonempty (Derivation (S pF pR (verifier f lhs rhs old a baseX))
  (.imp (UniformClosedPropositional.guards isS J.fval rawA rawB rawC)
   (.conj (.equal (LiteralCheckerAcceptance.runCall J.iteratorTag J.ptag index fuel code)
     (UniformClosedPropositionalCertificate.output isS J.ptag J.ctag J.atag rawA rawB rawC))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall J.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success J.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource
