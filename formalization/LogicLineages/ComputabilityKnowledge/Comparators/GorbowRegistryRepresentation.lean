module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentation

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryRepresentation
open GorbowSyntax GorbowStandardInstances GorbowTheoryProof GorbowRegistryDiagram
open LogicLineages.ComputabilityKnowledge.GorbowRegistryRepresentation

def ArithmeticInputs : Prop := ∀ s : Term 0, ArithmeticTerm s →
  (Nonempty (Derivation Theory (.universalRelation s)) ↔ GorbowSortedRegistry.relationProgram (inputValue s)=true) ∧
  (Nonempty (Derivation Theory (.neg (.universalRelation s))) ↔ GorbowSortedRegistry.relationProgram (inputValue s)=false) ∧
  (∀ m, Nonempty (Derivation Theory (.equal (.universalFunction s) (Term.numeral m))) ↔
    GorbowAtomicRegistry.functionProgram (inputValue s)=m)

def HeaderCalculation : Prop := ∀ arity tag args,
  ArithmeticTerm (headerInput arity tag args) ∧
  inputValue (headerInput arity tag args)=GorbowRegistryTuple.header arity tag args ∧
  GorbowArithmeticDerivation.Calculation (headerInput arity tag args) (GorbowRegistryTuple.header arity tag args)

def HeaderRepresentation : Prop := ∀ arity tag args,
  (Nonempty (Derivation Theory (.universalRelation (headerInput arity tag args))) ↔
    GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header arity tag args)=true) ∧
  (Nonempty (Derivation Theory (.neg (.universalRelation (headerInput arity tag args)))) ↔
    GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header arity tag args)=false) ∧
  (∀ m, Nonempty (Derivation Theory (.equal (.universalFunction (headerInput arity tag args)) (Term.numeral m))) ↔
    GorbowAtomicRegistry.functionProgram (GorbowRegistryTuple.header arity tag args)=m)

def CertificateExact : Prop := ∀ n code,
  (∃ c, check n code c=true) ↔ ∃ φ : Formula n,
    code=GorbowSortedSyntaxCode.formulaCode φ ∧ Nonempty (Derivation Theory φ)

def ConcreteCertificate : Prop := ∀ n (φ : Formula n),
  (∃ c, check n (GorbowSortedSyntaxCode.formulaCode φ) c=true) ↔ Nonempty (Derivation Theory φ)

def RejectContradiction : Prop := ∀ c, check 0 (GorbowSortedSyntaxCode.formulaCode falseEquality) c=false

def UniformCheck : Prop := Primrec (fun p : Nat × Nat × Nat => check p.1 p.2.1 p.2.2)

def Target : Prop := ArithmeticInputs ∧ HeaderCalculation ∧ HeaderRepresentation ∧ CertificateExact ∧
  ConcreteCertificate ∧ RejectContradiction ∧ UniformCheck
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowRegistryRepresentation
