module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB List.Vector

/-- Exact finite source-axiom codes. The empty disjunction is the arithmetic
contradiction, not an oracle predicate. Equality is oriented numeral=x for
literal source equality substitution. -/
def codeList : List Sentence → Formula 1
  | [] => .equal .zero (.succ .zero)
  | sigma :: rest => .disj
      (.equal (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)) (.var 0))
      (codeList rest)

/-- The original installed verifier at ONE fixed source fuel, retaining the
formula-code variable and binding only the certificate. -/
def fixedFuelProvability (pF : Program 1) (c : Code) (fuel : Nat) : Formula 1 :=
  .ex (.equal (GorbowPRDefiningEquations.call (GorbowNamedInternalProvability.checkerTag pF)
    (Term.numeral (Encodable.encode c) ::ᵥ Term.numeral fuel ::ᵥ Term.numeral 0 ::ᵥ
      .var 1 ::ᵥ .var 0 ::ᵥ nil)) (Term.numeral 1))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource
