module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP
open GorbowSyntax
/-- Fixed external sentences, but arbitrary internal index. The quotation
terms are the ORIGINAL sorted formula numerals, not raw-code surrogates.
Context zero is the ordinary sentence-provability convention. -/
def distribution {ctx : Nat} (vtag : Nat) (index : Term ctx) (sigma tau : Sentence) : Formula ctx :=
 .imp (ExistentialVerifierMP.provability vtag index .zero
  (Term.numeral (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau))))
  (.imp (ExistentialVerifierMP.provability vtag index .zero
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)))
   (ExistentialVerifierMP.provability vtag index .zero
    (Term.numeral (GorbowSortedSyntaxCode.formulaCode tau))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP
