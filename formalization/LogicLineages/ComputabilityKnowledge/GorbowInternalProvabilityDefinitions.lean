module

public import LogicLineages.ComputabilityKnowledge.GorbowPRNumeralCalculationDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode

@[expose] public section

/-! An actual existential proof-certificate formula in the unchanged Gorbow
language. The selected finite PR registry computes the existing numeric
Hilbert checker, rather than interpreting a new provability atom as truth.
This is a supplier for paper12, not source Base/DCB identification, internal
Hilbert--Bernays conditions, or a completed numbered source statement. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowInternalProvability
open GorbowSyntax GorbowPRProgram List.Vector

def arguments (formula certificate : Nat) : List.Vector Nat 2 :=
  formula ::ᵥ certificate ::ᵥ List.Vector.nil

def checkerValue (axCheck : List Nat → Bool) (formula certificate : Nat) : Nat :=
  if GorbowTheoryNumericCertificate.check axCheck 0 formula certificate then 1 else 0

def Represents (axCheck : List Nat → Bool) (p : Program 2) : Prop :=
  ∀ formula certificate, evaluate p (arguments formula certificate) =
    checkerValue axCheck formula certificate

/-- Under the existential binder, variable0 is the certificate and variable1
is the retained free formula-code variable. Registry tag0 is the actual root. -/
def body : Formula 2 :=
  .equal (GorbowPRDefiningEquations.call 0
    (.var 1 ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1)

def provabilityFormula : Formula 1 := .ex body

/-- A literal code instance, with only the certificate variable bound. -/
def atCode (formula : Nat) : Sentence :=
  .ex (.equal (GorbowPRDefiningEquations.call 0
    (Term.numeral formula ::ᵥ .var 0 ::ᵥ List.Vector.nil)) (Term.numeral 1))

end LogicLineages.ComputabilityKnowledge.GorbowInternalProvability
