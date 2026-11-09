module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry

/-- Checking the finite registry list names precisely the existing theory. -/
def ExactRegistryAxioms : Prop :=
  ∀ n (p : Program n) (sigma : Sentence),
    GorbowTheoryChecker.ProgramTheory (registryAxiomCheck p) sigma ↔
      GorbowPRNumeralCalculation.Theory p sigma

/-- Each fixed original AST/registry occurrence has ONE primitive-recursive
numeric certificate generator for all its numeral inputs. The program and
registry are quantified BEFORE the generator's Primrec condition. Merely
choosing a proof separately at each input does not establish this target. -/
def FixedProgramCertificates : Prop :=
  ∀ n (p : Program n) (tag : Nat) m (q : Program m),
    (nodes p)[tag]? = some ⟨m, q⟩ →
    ∃ produce : List.Vector Nat m → Nat,
      Primrec produce ∧ ∀ inputs : List.Vector Nat m,
      GorbowTheoryNumericCertificate.check (registryAxiomCheck p) 0
        (GorbowSortedSyntaxCode.formulaCode (calculation tag q inputs))
        (produce inputs) = true

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Targets
