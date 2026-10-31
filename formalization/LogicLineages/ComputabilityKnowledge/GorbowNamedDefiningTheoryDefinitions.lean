module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowBooleanTruth
public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions

@[expose] public section
/-! Literal universal named aliases appended to the NEW finite PR defining
theory, not to an old total ground-diagram theory. No source Base adequacy,
conservativity, or full-language/revision-ground identity is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory
open GorbowSyntax GorbowPRProgram GorbowSourceRegistryPadding List.Vector

def headerVariables (name : Nat × Nat) : Term name.1 :=
  GorbowRegistryTuple.headerTerm name.1 name.2
    (GorbowPRDefiningEquations.argumentVariables name.1).toList

def functionAlias (name : Nat × Nat) : Sentence :=
  GorbowPRDefiningEquations.equation (.universalFunction (headerVariables name))
    (GorbowPRDefiningEquations.call functionTag (headerVariables name ::ᵥ List.Vector.nil))

def relationAlias (pF : Program 1) (name : Nat × Nat) : Sentence :=
  GorbowStandardInduction.universalClosure (GorbowBooleanTruth.biconditional
    (.universalRelation (headerVariables name))
    (.equal (GorbowPRDefiningEquations.call (relationTag pF)
      (headerVariables name ::ᵥ List.Vector.nil)) (Term.numeral 1)))

def aliases (pF : Program 1) : List Sentence :=
  functionNames.map functionAlias ++ relationNames.map (relationAlias pF)

def axioms (pF pR : Program 1) : List Sentence :=
  GorbowPRDefiningEquations.axioms (root pF pR) ++ aliases pF

def Theory (pF pR : Program 1) : Sentence → Prop := fun sigma => sigma ∈ axioms pF pR

def check (pF pR : Program 1) (raw : List Nat) : Bool :=
  decide (raw ∈ (axioms pF pR).map GorbowFormulaPrefixCode.encode)

end LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory
