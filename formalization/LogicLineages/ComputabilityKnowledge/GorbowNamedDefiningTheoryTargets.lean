module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowSourceRegistryPadding GorbowTheoryProof

def InternalEquationsSound : Prop := ∀ (pF pR : Program 1) I sigma,
  sigma ∈ GorbowPRDefiningEquations.axioms (root pF pR) →
    sigma.realize (GorbowNamedRegistryInterpretation.interpretation pF pR I) Fin.elim0

def AliasesSound : Prop := ∀ (pF pR : Program 1) I sigma,
  sigma ∈ aliases pF → sigma.realize (GorbowNamedRegistryInterpretation.interpretation pF pR I) Fin.elim0

def TheorySoundness : Prop := ∀ (pF pR : Program 1) (sigma : Sentence),
  Derivation (Theory pF pR) sigma → ∀ I,
    sigma.realize (GorbowNamedRegistryInterpretation.interpretation pF pR I) Fin.elim0

def CheckExact : Prop := ∀ (pF pR : Program 1) raw,
  check pF pR raw = true ↔ ∃ sigma ∈ axioms pF pR, GorbowFormulaPrefixCode.encode sigma = raw

def FixedCheckerPrimitive : Prop := ∀ pF pR : Program 1, Primrec (check pF pR)

def ProofEmbedding : Prop := ∀ (pF pR : Program 1) (sigma : Sentence),
  Derivation (GorbowPRNumeralCalculation.Theory (root pF pR)) sigma →
    Nonempty (Derivation (Theory pF pR) sigma)

def InternalNumeralCertificates : Prop := ∀ (pF pR : Program 1) (tag : Nat) m (q : Program m),
  (nodes (root pF pR))[tag]? = some ⟨m,q⟩ → ∀ v : List.Vector Nat m,
    Nonempty (Derivation (Theory pF pR) (.equal
      (GorbowPRDefiningEquations.call tag (GorbowPRNumeralCalculation.numeralArguments v))
      (Term.numeral (evaluate q v)))) ∧
    ∀ value, evaluate q v ≠ value → Nonempty (Derivation (Theory pF pR) (.neg (.equal
      (GorbowPRDefiningEquations.call tag (GorbowPRNumeralCalculation.numeralArguments v))
      (Term.numeral value))))

def SpecificSourceModel : Prop := ∃ pF pR : Program 1,
  (∀ name ∈ functionNames, ∀ args : List Nat, args.length = name.1 →
    GorbowNamedRegistryInterpretation.functionProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) =
      sourceFunction (GorbowRegistryTuple.header name.1 name.2 args)) ∧
  (∀ name ∈ relationNames, ∀ args : List Nat, args.length = name.1 →
    GorbowNamedRegistryInterpretation.relationProgram pF pR (GorbowRegistryTuple.header name.1 name.2 args) =
      GorbowSortedRegistry.relationProgram (GorbowRegistryTuple.header name.1 name.2 args)) ∧
  ∀ (sigma : Sentence), Derivation (Theory pF pR) sigma → ∀ I,
    sigma.realize (GorbowNamedRegistryInterpretation.interpretation pF pR I) Fin.elim0

end LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.Targets
