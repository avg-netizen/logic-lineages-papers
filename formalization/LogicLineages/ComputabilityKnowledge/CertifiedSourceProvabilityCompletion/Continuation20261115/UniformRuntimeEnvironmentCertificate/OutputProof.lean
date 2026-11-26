module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.OutputProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPRDefiningEquations SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual original right projection of the runtime fold is identified by its
entire packed-state equation, with appendNil paid internally. -/
theorem substituted {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 (replacement : Term ctx) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag
    (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e) replacement)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag (replacement ::ᵥ raw) f
    (UniformRuntimeEnvironmentAgreement.specialize e)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let A := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let B := FixedFormulaSubstitution.formulaValue I.ctag I.atag (replacement ::ᵥ raw) f
  (UniformRuntimeEnvironmentAgreement.specialize e)
 let state : Term ctx := .succ (LiteralSyntaxValidator.FormulaBindingProof.taskList I.ptag I.ctag (.succ .zero))
 let packed := HistoryKernel.pairCall I.ptag state (.zero : Term ctx)
 obtain ⟨hag⟩ := UniformRuntimeEnvironmentAgreement.StatementChecks.exactRuntimeEnvironmentAgreement arity p
  I.ftag I.etag I.vtag I.stepTag I.stag I.ptag I.ctag I.atag I.dtag I.len I.qtag I.ltag I.rtag
  I.h_ftag I.h_etag I.h_vtag I.h_stepTag I.h_stag I.h_ptag I.h_ctag I.h_atag I.h_dtag
  I.h_len I.h_qtag I.h_ltag I.h_rtag n 0 inputs e f ctx G raw replacement .zero .zero hinputs
 have hfold : Hilbert.Local T ctx G
  (.equal (UniformClosedSubstitutionRawFold.foldCall I.ftag A packed replacement)
   (HistoryKernel.pairCall I.ptag (.succ .zero) (HistoryAppend.appendCall I.atag .zero B))) := by
  simpa only [UniformRuntimeEnvironmentAgreement.agreement,UniformRuntimeEnvironmentAgreement.initial,
   A,B,packed,state,LiteralSyntaxValidator.FormulaBindingProof.taskList,LiteralSyntaxStep.taskCall,
   Nat.zero_add,Term.numeral] using hag
 have hproject := callCongruence (T := T) (G := G) I.rtag
  (UniformClosedSubstitutionRawFold.foldCall I.ftag A packed replacement ::ᵥ nil)
  (HistoryKernel.pairCall I.ptag (.succ (.zero : Term ctx)) (HistoryAppend.appendCall I.atag .zero B) ::ᵥ nil)
  (fun i => by
   cases i using Fin.cases with
   | zero => exact hfold
   | succ i => exact Fin.elim0 i)
 obtain ⟨hdecode⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.rtag I.ptag true I.h_rtag I.h_ptag
  (.succ (.zero : Term ctx)) (HistoryAppend.appendCall I.atag .zero B)
 obtain ⟨hnil⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil arity p I.atag I.h_atag ctx B
 exact ⟨localTrans _ _ _ hproject (localTrans _ _ _ (.base hdecode) (.base hnil))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.OutputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.OutputProof
