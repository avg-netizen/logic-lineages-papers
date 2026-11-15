module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.FoldProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionRawFold.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion
open GorbowSyntax SixSol20261113
/-- Concatenate original encoded input lists, preserving the entire actual
packed output state and the same replacement. This is not output framing. -/
def fusion {ctx : Nat} (ftag atag : Nat)
 (leftTokens rightTokens packed replacement : Term ctx) : Formula ctx :=
 .equal (UniformClosedSubstitutionRawFold.foldCall ftag
  (HistoryAppend.appendCall atag leftTokens rightTokens) packed replacement)
  (UniformClosedSubstitutionRawFold.foldCall ftag rightTokens
   (UniformClosedSubstitutionRawFold.foldCall ftag leftTokens packed replacement) replacement)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRawFoldInputFusion
