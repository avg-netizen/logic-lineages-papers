module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBasePublishedPackage.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

/-- Five actual runtime inputs: outer/box/CK second-child offsets, r, s.
Neither the selected final pF AST nor its size is embedded in these programs. -/
def pairInputs : Fin 2 → Program 5 := (Program.projection (3 : Fin 5) ::ᵥ Program.projection (4 : Fin 5) ::ᵥ nil).get
def headerValue : Program 5 :=
 .composition (ArithmeticTemplateEvaluation.valueProgram CurrentNamedHeaderCertificate.template) pairInputs
def rawHeader : Program 5 := applyOne LiteralNumeralPrefix.numeralCode headerValue
def rawCall (tag : Nat) : Program 5 :=
 CurrentCompositionProducerProgram.callCode (constant 5 tag) (rawHeader ::ᵥ nil)
def peel (tag : Nat) (offsetIndex : Fin 5) : Program 5 :=
 .composition RuntimeOffsetAugmentationProducer.program
  (constant 5 tag ::ᵥ .projection offsetIndex ::ᵥ headerValue ::ᵥ nil).get
def peelCertificate : Program 5 :=
 CurrentRecursionBaseProgram.transitivity (rawCall 6) (rawCall 10) (rawCall 12)
  (CurrentRecursionBaseProgram.transitivity (rawCall 6) (rawCall 8) (rawCall 10) (peel 6 0) (peel 8 1))
  (peel 10 2)
def output (pF0 : Program 1) : Program 5 := applyOne LiteralNumeralPrefix.numeralCode (applyOne pF0 headerValue)
def baseCertificate (pF0 : Program 1) : Program 5 :=
 .composition (CurrentStructuralProducerCompiler.compile pF0) (constant 5 12 ::ᵥ headerValue ::ᵥ nil).get
def calculation (pF0 : Program 1) : Program 5 :=
 CurrentRecursionBaseProgram.transitivity (rawCall 6) (rawCall 12) (output pF0)
  peelCertificate (baseCertificate pF0)
/-- Literal producer compiled before source selection, depending only on retained
primitive pF0. All other AST components are fixed previously checked programs. -/
def program (pF0 : Program 1) : Program 5 :=
 CurrentRecursionBaseProgram.transitivity
  (.composition CurrentNamedHeaderTransport.leftQuote pairInputs) (rawCall 6) (output pF0)
  (.composition CurrentNamedHeaderTransport.program pairInputs) (calculation pF0)

def extra (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3) (pF0 : Program 1) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,RetainedBaseProducerInstallation.extra f lhs rhs CurrentNamedHeaderCertificate.template old a baseX pF0⟩,
   ⟨5,program pF0⟩]
def selected (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 : Program 1) (pCK : Program 2) (pG : Program 6) : Program 1 :=
 GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK)
  (InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0))
def secondOffset {n : Nat} (p : Program 1) (q : Program n) : Nat :=
 argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1
def inputs {ctx : Nat} (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (outer : Program 5)
 (r s : Term ctx) : List.Vector (Term ctx) 5 :=
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 let pF := GorbowNamedInternalProvability.augment inner box
 Term.numeral (secondOffset pF outer) ::ᵥ Term.numeral (secondOffset inner box) ::ᵥ
 Term.numeral (secondOffset pF0 pCK) ::ᵥ r ::ᵥ s ::ᵥ nil

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer
