module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralTagTargets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.FiniteSourceDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeDefinitions
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseDefinitions

@[expose] public section
/-! One actual source registry containing BOTH its retained-parameter CK code
program and a numeric computation-certificate producer. These external
contracts do not assert internally quantified symbolic checker correctness. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB List.Vector

/-- Six inputs are the RUNTIME q occurrence tag followed by q's five inputs. -/
def ProducerFor (q : Program 5) (pG : Program 6) : Prop :=
  ∀ n (p : Program n) tag, (nodes p)[tag]? = some ⟨5,q⟩ →
    ∀ inputs : List.Vector Nat 5,
    GorbowTheoryNumericCertificate.check (EffectiveNumeral.registryAxiomCheck p) 0
      (GorbowSortedSyntaxCode.formulaCode (EffectiveNumeral.calculation tag q inputs))
      (evaluate pG (tag ::ᵥ inputs)) = true

def RegistryInstall (pF pR : Program 1) (q : Program 5) (tagG : Nat) (pG : Program 6) : Prop :=
  (nodes (GorbowSourceRegistryPadding.root (augmented pF q) pR))[tagG]? = some ⟨6,pG⟩

def generatedCertificate (pF : Program 1) (pG : Program 6) (inputs : List.Vector Nat 5) : Nat :=
  evaluate pG (GorbowNamedInternalProvability.checkerTag pF ::ᵥ inputs)

def generatedFormulaCode (pF : Program 1) (q : Program 5) (inputs : List.Vector Nat 5) : Nat :=
  GorbowSortedSyntaxCode.formulaCode
    (EffectiveNumeral.calculation (GorbowNamedInternalProvability.checkerTag pF) q inputs)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InstalledProducer
