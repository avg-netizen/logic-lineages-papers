module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Exact literal predecessor(case13 [formula,replacement]) graph under only
original formula1/term0 guards. Head/tail/length2 and Option Some must be derived
internally on the actual two-cons list; no canonical-list premise is added. -/
def InternalConclusionGraph : Prop := ∀ n (p : Program n) (I : GraphInstallation p),
 ∀ ctx (formula replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.equal (compiledConclusion I formula replacement) (expandedConclusion I formula replacement))))
/-- Actual formulaValidator0 of the literal compiled conclusion, not a native
Formula image and not a substitute symbolic conclusion. Arbitrary runtime codes
and exact original guards; no scanner-success or validity premise for output. -/
def InternalConclusionValidity : Prop := ∀ n (p : Program n) (I : Installation p),
 ∀ ctx (formula replacement : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedInstanceRecognizer.guards I.fval I.vtag formula replacement)
   (.equal (LiteralSyntaxValidator.formulaCall I.fval .zero
    (compiledConclusion I.toGraphInstallation formula replacement)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Validity.Targets
