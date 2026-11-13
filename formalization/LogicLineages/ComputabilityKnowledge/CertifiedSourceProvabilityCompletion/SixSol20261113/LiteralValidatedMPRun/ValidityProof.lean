module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.LiteralValidatorSpecialization.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryLengthOffset HistoryCodec.ArithmeticSupport
open LiteralRawMP LiteralMPRun

theorem internalNewLineValidity : Targets.InternalNewLineValidity := by
 intro l a x n p itag ltag atag ptag ctag dtag droptag rtag tag hi hl ha hp hc hd hdrop hr ht ctx context phi psi imp ant tailI tailA index fuel
 let T := GorbowPRNumeralCalculation.Theory p
 let H := inputRuns itag atag ptag ctag context phi psi imp ant tailI tailA index fuel
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have hI := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 have hA := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 let iv := HistoryTopProvenance.validityTag itag validity l a x
 have hiv := HistoryTopProvenance.OccurrenceProof.actualValidityOccurrence validity l a x n p itag hi
 let ftag := HistoryTopProvenance.LiteralValidatorSpecialization.formulaTag itag l a x
 have hf := HistoryTopProvenance.LiteralValidatorSpecialization.OccurrenceProof.actualFormulaOccurrence l a x n p itag hi
 let args : Fin 2 → Program 1 := Fin.cases LiteralSyntaxValidator.lineContext (Fin.cases LiteralSyntaxValidator.lineRaw Fin.elim0)
 let leftTag := iv+argumentTag LiteralSyntaxValidator.formulaValidator args 0
 have hleft : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩ :=
  Equations.argumentChild p iv LiteralSyntaxValidator.formulaValidator args hiv 0
 obtain ⟨hvalidI⟩ := HistoryTopProvenance.LiteralValidatorSpecialization.Proof.internalFullRunFormulaValidity
  l a x n p itag ptag ctag leftTag dtag hi hp hc hleft hd ctx imp context (implicationRaw atag ctag phi psi) tailI index fuel
 obtain ⟨hvalidA⟩ := HistoryTopProvenance.LiteralValidatorSpecialization.Proof.internalFullRunFormulaValidity
  l a x n p itag ptag ctag leftTag dtag hi hp hc hleft hd ctx ant context phi tailA index fuel
 have hfi := Hilbert.Local.mp (.base hvalidI) hI
 have hfa := Hilbert.Local.mp (.base hvalidA) hA
 obtain ⟨hclosure⟩ := LiteralSyntaxValidator.ImplicationProof.internalImplicationConclusion n p ftag atag ctag hf ha hc ctx context phi psi
 have hpsi := Hilbert.Local.mp (.mp (.base hclosure) hfa) hfi
 let g : Fin 3 → Program 4 := Fin.cases (applyOne validity HistoryDispatcher.lineCode)
  (Fin.cases (constant 4 0) (Fin.cases (HistoryDispatcher.ruleDispatcher l a x) Fin.elim0))
 have hw := Equations.argumentChild p tag HistoryCodec.select g ht 0
 have hvnode : (nodes p)[LiteralRawMP.validityTag tag validity l a x]? = some ⟨1,validity⟩ :=
  Equations.functionChild p _ validity (fun _ => HistoryDispatcher.lineCode) hw
 let payload := HistoryKernel.pairCall ptag (.succ (.succ .zero)) (HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag .zero (HistoryKernel.pairCall ptag (lengthCall ltag ant) .zero)))
 obtain ⟨hbinding⟩ := LiteralSyntaxValidator.LineBindingProof.internalLineBinding n p
  (LiteralRawMP.validityTag tag validity l a x) ftag ptag hvnode hf hp ctx context psi payload
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base hbinding) hpsi))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedMPRun.ValidityProof
