module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof

theorem internalTopFormulaValidity : Targets.InternalTopFormulaValidity := by
 intro l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr ctx count lines context raw tail remaining index fuel
 have hline := HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence
   LiteralSyntaxValidator.lineValidator l a x n p itag hi
 have hformula := OccurrenceProof.actualFormulaOccurrence l a x n p itag hi
 obtain ⟨hw⟩ := WitnessProof.witnessValid p
   (validityTag itag LiteralSyntaxValidator.lineValidator l a x)
   (formulaTag itag l a x) ptag leftTag rightTag hline hformula hp hl hr context raw
 obtain ⟨ht⟩ := HistoryTopProvenance.Proof.internalTopProvenance
   LiteralSyntaxValidator.lineValidator l a x n p itag ptag ctag leftTag rightTag
   hi hp hc hl hr ctx count lines context raw tail remaining index fuel
 unfold provenance at ht
 exact ⟨Hilbert.compose hw ht⟩

theorem internalFullRunFormulaValidity : Targets.InternalFullRunFormulaValidity := by
 intro l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr ctx lines context raw tail index fuel
 exact internalTopFormulaValidity l a x n p itag ptag ctag leftTag rightTag hi hp hc hl hr
   ctx lines lines context raw tail .zero index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Proof
