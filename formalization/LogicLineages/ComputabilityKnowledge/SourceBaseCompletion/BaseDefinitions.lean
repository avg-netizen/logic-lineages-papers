module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedKTDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesDefinitions

@[expose] public section
/-! Exact source-Base obligations on the unchanged published construction.
PA(L), including induction in the entire language, is already intrinsic to
Derivation.arithmetic. Base below is therefore ONLY its extra definitional
syntax axioms. The finite list is not a replacement for PA(L).
No source representation, modelhood, proof translation or HB field is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.SourceBaseCompletion
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowNamedNumeralCertificates GorbowSourceRegistryPadding

def Base (pF pR : Program 1) (q : Program 5) : Sentence → Prop :=
  GorbowNamedDefiningTheory.Theory (augmented pF q) pR

/-- All declared source syntax functions, on every numeric argument vector,
have their exact positive and negative numeral representations in Base. -/
def FunctionRepresentations (pF pR : Program 1) (q : Program 5) : Prop :=
  ∀ name ∈ functionNames, ∀ (v : List.Vector Nat name.1) value,
    (Nonempty (Derivation (Base pF pR q) (functionSentence name v value)) ↔
      sourceFunction (inputCode name v) = value) ∧
    (Nonempty (Derivation (Base pF pR q) (.neg (functionSentence name v value))) ↔
      sourceFunction (inputCode name v) ≠ value)

/-- All declared source syntax predicates, with both polarities and exact
standard-N meanings. No restriction to selected literal sentences. -/
def RelationRepresentations (pF pR : Program 1) (q : Program 5) : Prop :=
  ∀ name ∈ relationNames, ∀ v : List.Vector Nat name.1,
    (Nonempty (Derivation (Base pF pR q) (relationSentence name v)) ↔
      GorbowSortedRegistry.relationProgram (inputCode name v) = true) ∧
    (Nonempty (Derivation (Base pF pR q) (.neg (relationSentence name v))) ↔
      GorbowSortedRegistry.relationProgram (inputCode name v) = false)

/-- The fixed revision ground agrees with every named syntax symbol, at
every input, while its other raw-header behavior remains unchanged. -/
def GroundRepresentations (pF pR : Program 1) (q : Program 5) : Prop :=
  (∀ name ∈ functionNames, ∀ args : List Nat, args.length = name.1 →
    (GorbowPublishedModel.ground pF pR q).universalFunction
        (GorbowRegistryTuple.header name.1 name.2 args) =
      sourceFunction (GorbowRegistryTuple.header name.1 name.2 args)) ∧
  (∀ name ∈ relationNames, ∀ args : List Nat, args.length = name.1 →
    ((GorbowPublishedModel.ground pF pR q).universalRelation
        (GorbowRegistryTuple.header name.1 name.2 args) ↔
      GorbowSortedRegistry.relationProgram
        (GorbowRegistryTuple.header name.1 name.2 args) = true))

def SyntaxAdequate (pF pR : Program 1) (q : Program 5) : Prop :=
  FunctionRepresentations pF pR q ∧ RelationRepresentations pF pR q ∧
    GroundRepresentations pF pR q

end LogicLineages.ComputabilityKnowledge.SourceBaseCompletion
