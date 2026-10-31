module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates.Targets
open GorbowSyntax GorbowPRProgram GorbowSourceRegistryPadding GorbowTheoryProof List.Vector
open GorbowNamedDefiningTheory (Theory)

def NamedFunctionCalculation : Prop := ∀ (pF pR : Program 1) name, name ∈ functionNames →
  ∀ v : List.Vector Nat name.1, Nonempty (Derivation (Theory pF pR)
    (functionSentence name v (evaluate pF (inputCode name v ::ᵥ List.Vector.nil))))

def NamedFunctionRefutation : Prop := ∀ (pF pR : Program 1) name, name ∈ functionNames →
  ∀ (v : List.Vector Nat name.1) value,
    evaluate pF (inputCode name v ::ᵥ List.Vector.nil) ≠ value →
      Nonempty (Derivation (Theory pF pR) (.neg (functionSentence name v value)))

def NamedRelationCalculation : Prop := ∀ (pF pR : Program 1) name, name ∈ relationNames →
  ∀ v : List.Vector Nat name.1,
    (evaluate pR (inputCode name v ::ᵥ List.Vector.nil) = 1 →
      Nonempty (Derivation (Theory pF pR) (relationSentence name v))) ∧
    (evaluate pR (inputCode name v ::ᵥ List.Vector.nil) ≠ 1 →
      Nonempty (Derivation (Theory pF pR) (.neg (relationSentence name v))))

def SpecificSourceCertificates : Prop := ∃ pF pR : Program 1,
  (∀ name ∈ functionNames, ∀ v : List.Vector Nat name.1,
    Nonempty (Derivation (Theory pF pR) (functionSentence name v (sourceFunction (inputCode name v)))) ∧
    ∀ value, sourceFunction (inputCode name v) ≠ value →
      Nonempty (Derivation (Theory pF pR) (.neg (functionSentence name v value)))) ∧
  (∀ name ∈ relationNames, ∀ v : List.Vector Nat name.1,
    (GorbowSortedRegistry.relationProgram (inputCode name v) = true →
      Nonempty (Derivation (Theory pF pR) (relationSentence name v))) ∧
    (GorbowSortedRegistry.relationProgram (inputCode name v) = false →
      Nonempty (Derivation (Theory pF pR) (.neg (relationSentence name v)))))

end LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificates.Targets
