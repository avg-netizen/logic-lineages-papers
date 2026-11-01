module

public import LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentationDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.Targets
open GorbowSyntax

def LiteralInstance : Prop := ∀ (template : Formula 1) c,
  instanceRaw template c = some (GorbowFormulaPrefixCode.encode
    (GorbowStandardInstances.instantiate template (Term.numeral (Encodable.encode c))))

def UniformRawChecker : Prop := ∀ (base : List Sentence) (template : Formula 1),
  Primrec (fun p : Code × List Nat => check base template p.1 p.2)

def UniformNumericChecker : Prop := ∀ (base : List Sentence) (template : Formula 1),
  Primrec (fun p : Code × Nat => numericCheck base template p.1 p.2)

/-- An actual total ordinary program, not an assumed index or a conditionally
well-founded definition of a theory. -/
def ActualFixedPoint : Prop := ∀ (base : List Sentence) (template : Formula 1),
  ∃ c : Code, ∀ input, c.eval input = Part.some (numericCheck base template c input)

/-- The exact accepted literal axiom theory is the intended finite list plus
the template carrying this very same ordinary program index. -/
def ExactPresentedTheory : Prop := ∀ (base : List Sentence) (template : Formula 1),
  ∃ c : Code,
    (∀ input, c.eval input = Part.some (numericCheck base template c input)) ∧
    GorbowEnumeratedProvability.enumeratedTheory c = Theory base template c ∧
    GorbowTheoryChecker.ProgramTheory (check base template c) = Theory base template c

def Target : Prop := LiteralInstance ∧ UniformRawChecker ∧ UniformNumericChecker ∧
  ActualFixedPoint ∧ ExactPresentedTheory

end LogicLineages.ComputabilityKnowledge.GorbowSelfIndexedPresentation.Targets
