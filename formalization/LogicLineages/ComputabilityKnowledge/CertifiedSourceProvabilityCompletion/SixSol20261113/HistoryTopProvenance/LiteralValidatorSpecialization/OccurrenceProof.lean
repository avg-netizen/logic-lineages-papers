module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.OccurrenceProof
open GorbowPRProgram GorbowPRRegistry

theorem actualFormulaOccurrence : Targets.ActualFormulaOccurrence := by
 intro l a x n p itag hi
 have hv := HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence
   LiteralSyntaxValidator.lineValidator l a x n p itag hi
 exact SixSol20261112.Fuel.Equations.functionChild p
   (validityTag itag LiteralSyntaxValidator.lineValidator l a x)
   LiteralSyntaxValidator.formulaValidator
   (Fin.cases LiteralSyntaxValidator.lineContext (Fin.cases LiteralSyntaxValidator.lineRaw Fin.elim0)) hv
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.OccurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.OccurrenceProof
