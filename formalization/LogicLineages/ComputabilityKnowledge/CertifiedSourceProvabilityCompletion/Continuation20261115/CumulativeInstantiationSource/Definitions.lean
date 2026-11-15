module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
abbrev logical (lhs rhs : Term 1) (old : Program 1) : Program 1 :=
 RawEqualityInstantiationAcceptance.logicalLeaf lhs rhs (CumulativeInstantiationRegistry.previousLogical old)
abbrev arithmetic (a : Program 1) : Program 1 := RawMulNewestAddition.arithmetic a
abbrev verifier (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) : Program 5 :=
 RawEqualityInstantiationCertificate.verifier lhs rhs (CumulativeInstantiationRegistry.previousLogical old)
  (arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
abbrev root (lhs rhs : Term 1) (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier lhs rhs old a baseX)) pR
/-- This extra finite carrier is fixed BEFORE the published source tuple/tags.
The MP constructor is included explicitly; no inherited record field is presumed. -/
def extra {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨4,LiteralRawMP.constructor⟩,
  ⟨6,CumulativeInstantiationRegistry.carrier lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)⟩]
/-- All six prior source packages at the identical NEW tuple and literal leaves. -/
def Packages (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (mtag xtag : Nat) : Prop :=
 let l := logical lhs rhs old
 let ar := arithmetic a
 let x := SaturatedAxiomLeaf.saturated baseX
 LiteralValidatedSource.Targets.ValidatorPackage l ar x offset pF pR ∧
 LiteralSourceCoreMP.Targets.MPPackage l ar x offset pF pR mtag ∧
 LiteralSourceFuelWitness.Targets.WitnessPackage l ar x pF pR ∧
 SaturatedAxiomSource.Targets.AxiomPackage l ar baseX pF pR xtag ∧
 SaturatedSourceMP.Targets.ClosurePackage l ar baseX offset pF pR mtag ∧
 PublishedSourceHB2.Targets.HB2Package l ar baseX pF pR c
/-- Actual unchanged arithmetic certificate program checked by the new CORE. -/
def CompilerCapability {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (pF pR : Program 1)
 (I : CumulativeInstantiationRegistry.JointInstallation (root lhs rhs pF pR old a x) lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier lhs rhs old a x))
 (.conj (RawReflexivityDispatcher.valid I.previous.validatorTag (GorbowPRDefiningEquations.call I.template.quoteTag values))
  (RawEqualityComposition.accepted I.current.qctag I.previous.consTag I.previous.appendTag index fuel
   (GorbowPRDefiningEquations.call I.template.quoteTag values)
   (LiteralNumeralPrefix.numeralCall I.previous.numeralTag (ArithmeticTemplateEvaluation.instantiatedValue t values))
   (GorbowPRDefiningEquations.call I.template.certificateTag values))))
/-- Literal fixed-tag13 singleton certificate at the same selected new CORE. -/
def InstantiationCapability {k : Nat} (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (x : Program 3)
 (pF pR : Program 1)
 (I : CumulativeInstantiationRegistry.JointInstallation (root lhs rhs pF pR old a x) lhs rhs t old a (SaturatedAxiomLeaf.saturated x)) : Prop :=
 ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier lhs rhs old a x))
 (.imp (RawReflexivityDispatcher.valid I.current.vtag raw)
  (.equal (LiteralCheckerAcceptance.coreCall I.current.qctag index fuel .zero
   (.add (RawEqualityInstantiation.formulaValue I.current.ctag I.current.atag lhs rhs raw)
    (RawEqualityInstantiation.formulaValue I.current.ctag I.current.atag lhs rhs raw))
   (RawEqualityInstantiationCertificate.certificate I.current.ctag I.current.qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationSource
