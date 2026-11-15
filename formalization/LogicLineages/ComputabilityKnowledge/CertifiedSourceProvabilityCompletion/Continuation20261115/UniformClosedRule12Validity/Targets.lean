module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Same literal predecessor(case12 triple); both original Option-success
branches and length/head/tail equations must be derived internally. -/
def InternalConclusionGraph : Prop := ∀ n (p : Program n) (I : GraphInstallation p),
 ∀ ctx (formula left right : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula left right)
   (.equal (compiledConclusion I formula left right) (expandedConclusion I formula left right))))
/-- Actual formulaValidator0 of the SAME compiled conclusion on arbitrary raw
terms, guarded only by original formula1/term0/term0 predicates. -/
def InternalConclusionValidity : Prop := ∀ n (p : Program n) (I : Installation p),
 ∀ ctx (formula left right : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedRule12.guards I.fval I.vtag formula left right)
   (.equal (LiteralSyntaxValidator.formulaCall I.fval .zero
    (compiledConclusion I.toGraphInstallation formula left right)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12Validity.Targets
