module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSourceDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

/-- The auxiliary finite formula recognizes precisely the actual source's
extra-axiom code set, in every standard interpretation. -/
def ExactFiniteCodes : Prop :=
  ∀ (sentences : List Sentence) (I : Interpretation) (code : Nat),
    (codeList sentences).realize I (Fin.cases code Fin.elim0) ↔
      ∃ sigma ∈ sentences, GorbowSortedSyntaxCode.formulaCode sigma = code

/-- A genuine INTERNAL source-axiom rule with a symbolic formula-code input,
at the SAME bound that covers every extra S axiom. This excludes intrinsic
logical/PA schema verification, arbitrary certificate preservation, HB2/HB3,
and the final source-collapse conclusions. -/
def ActualInternalFiniteAxioms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∃ fuel : Nat,
    (∀ sigma : Sentence, S pF pR q sigma ↔
      GorbowEnumeratedProvability.boundedTheory (c, fuel) sigma) ∧
    Nonempty (Derivation (S pF pR q) (.all
      (.imp (codeList (axiomsS pF pR q)) (fixedFuelProvability pF c fuel))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSource.Targets
