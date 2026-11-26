module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Both inventories are constructed from native leaves and retained pF0 before
choosing final pF or c. The second already includes checker/quantifier programs. -/
def extra (f : Formula 1) (lhs rhs : Term 1) (rawOld a : Program 1) (baseX : Program 3) (pF0 : Program 1) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,InstalledLiteralBinaryProducer.extra f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX pF0⟩,
   ⟨6,CurrentPublishedProvabilityIntroduction.extra f lhs rhs CurrentNamedHeaderCertificate.template rawOld a baseX⟩]
def selected (f : Formula 1) (lhs rhs : Term 1) (rawOld a : Program 1) (baseX : Program 3)
 (pF0 : Program 1) (pCK : Program 2) (pG : Program 6) : Program 1 :=
 InstalledLiteralBinaryProducer.SelectionProof.selectWith (extra f lhs rhs rawOld a baseX) pF0 pCK pG
/-- The explicit certified input to the original published-introduction program,
not an additional uninstalled whole-source compiler. -/
def inputCode {ctx : Nat} (K : Tags) (rule13Tag headerTag : Nat)
 (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (q : Program 5)
 (peelTag baseTag checkerTag : Nat) (pF : Program 1) (c : Code) (sigma : Sentence)
 (innerFuel innerCert : Term ctx) : Term ctx :=
 LiteralCheckerSuccessBridge.certificate K pF c sigma innerFuel innerCert
  (RetainedBaseLiteralBinary.certificate K rule13Tag headerTag pF0 pCK box q peelTag baseTag
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c)))
   (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))
  (CurrentCheckerSuccessCertificate.proofCode checkerTag pF c innerFuel
   (LiteralCheckerSuccessBridge.value pF c sigma) innerCert)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness
