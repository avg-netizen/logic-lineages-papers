module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
/-- Literal two-branch augmentation; no compiler for either child is assumed. -/
def branches {n : Nat} (p : Program 1) (q : Program n) : Fin 2 → Program 1 :=
 Fin.cases p (fun _ => GorbowNamedInternalProvability.wrapper q)
def projectionFormula (tag : Nat) : Formula 2 :=
 .equal (call (tag+1) (argumentVariables 2)) (.var 0)
def left {ctx : Nat} (K : Tags) (tag : Nat) (input : Term ctx) : Term ctx :=
 callValue K (Term.numeral tag) (LiteralNumeralPrefix.numeralCall K.numeralTag input ::ᵥ nil)
def children {n ctx : Nat} (K : Tags) (p : Program 1) (q : Program n) (tag : Nat) (input : Term ctx) :=
 CurrentCompositionCertificate.childValues K (.projection (0 : Fin 2)) (branches p q) tag
  (LiteralNumeralPrefix.numeralCall K.numeralTag input ::ᵥ nil)
def middle {n ctx : Nat} (K : Tags) (p : Program 1) (q : Program n) (tag : Nat) (input : Term ctx) :=
 callValue K (Term.numeral (tag+1)) (children K p q tag input)
def right {n ctx : Nat} (K : Tags) (p : Program 1) (q : Program n) (tag : Nat) (input : Term ctx) :=
 (children K p q tag input).get 0
/-- Two genuine defining-axiom specializations followed by transitivity.
The unused wrapper is quoted as syntax, never evaluated. The separate rule13Tag
is used only for binder specialization; K.constructorTag is the rule12 transitivity address. -/
def certificate {n ctx : Nat} (K : Tags) (rule13Tag : Nat) (p : Program 1) (q : Program n) (tag : Nat) (input : Term ctx) :=
 let root := PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
  (CurrentCompositionCertificate.rootFormula (.projection (0 : Fin 2)) (branches p q) tag)
  (LiteralNumeralPrefix.numeralCall K.numeralTag input ::ᵥ nil)
 let proj := PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
  (projectionFormula tag) (children K p q tag input)
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  (left K tag input) (middle K p q tag input) (right K p q tag input) root proj
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure
