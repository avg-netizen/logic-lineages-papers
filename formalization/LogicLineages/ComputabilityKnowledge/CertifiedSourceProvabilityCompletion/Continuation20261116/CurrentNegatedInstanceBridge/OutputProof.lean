module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.TokenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.OutputProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryLookup.DestructorProof (unaryCallCongruence)
open UniformClosedRule13Validity.GraphProof (binaryCongruence)
noncomputable def foldState {ctx : Nat} {T : Sentence → Prop} (ftag : Nat) (tokens a b raw : Term ctx)
 (h : Derivation T (.equal a b)) :
 Derivation T (.equal (UniformClosedSubstitutionRawFold.foldCall ftag tokens a raw)
  (UniformClosedSubstitutionRawFold.foldCall ftag tokens b raw)) := by
 apply Logic.callCongruence T ftag
 intro i
 cases i using Fin.cases with
 | zero => exact .logical (.reflexive tokens)
 | succ i => cases i using Fin.cases with
  | zero => exact h
  | succ i => cases i using Fin.cases with
   | zero => exact .logical (.reflexive raw)
   | succ i => exact Fin.elim0 i

theorem negatedOutput {n ctx : Nat} (p : Program n) (I : UniformClosedRule13Validity.Installation p)
 (matrix witness : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag (negValue I.ctag matrix) witness)
   (negValue I.ctag (UniformClosedInstanceRecognizer.outputValue I.ftag I.ptag I.ctag I.rtag matrix witness)))) := by
 let state : Term ctx := .succ (TokenProof.tasks I)
 let pre : Term ctx := TokenProof.tokenPrefix I
 let init := HistoryKernel.pairCall I.ptag state .zero
 let final := UniformClosedSubstitutionRawFold.foldCall I.ftag matrix init witness
 obtain ⟨_,hcons⟩ := UniformClosedSubstitutionRawFold.StatementChecks.exactRawRecursion n p I.ftag I.ptag I.ctag
  I.stepTag I.etag I.atag I.h_ftag I.h_ptag I.h_ctag I.h_stepTag I.h_etag I.h_atag
  ctx (Term.numeral 6) matrix state .zero witness
 obtain ⟨hcons⟩ := hcons
 obtain ⟨hs⟩ := TokenProof.step (ctx := ctx) p I
 obtain ⟨he⟩ := TokenProof.emit p I witness
 obtain ⟨hz⟩ := HistoryAppend.AppendEquationsProof.internalAppendNil n p I.atag I.h_atag ctx
  (UniformClosedSubstitutionEmit.emitCall I.etag state (Term.numeral 6) witness)
 have hacc := Logic.trans _ _ _ hz he
 have hnext := binaryCongruence I.ptag _ _ state pre hs hacc
 have hstart := Logic.trans _ _ _ hcons (foldState I.ftag matrix _ _ witness hnext)
 obtain ⟨hframe⟩ := InlineFrame.AtomsProof.outputEquation p I.ptag I.atag I.ltag I.rtag
  I.h_ptag I.h_ltag I.h_rtag pre state (.zero : Term ctx)
 obtain ⟨hpre⟩ := LiteralSyntaxValidator.QuantifierOperationalProof.singletonAppendNil p I.atag I.ctag
  I.h_atag I.h_ctag (Term.numeral 6 : Term ctx)
 have hnorm := binaryCongruence I.ptag state _ state pre (.logical (.reflexive state)) hpre
 have hinit := Logic.trans _ _ _ hframe hnorm
 obtain ⟨hcommute⟩ := InlineFrame.RawProof.rawFrame p I matrix pre init witness
 have hmiddle := Logic.trans _ _ _ (foldState I.ftag matrix _ _ witness (Support.equalitySymmetry _ _ hinit)) hcommute
 have hproject := unaryCallCongruence I.rtag _ _ (Logic.trans _ _ _ hstart hmiddle)
 obtain ⟨hproj⟩ := HistoryLookup.DestructorProof.decoderCrossPair p I.rtag I.ptag true I.h_rtag I.h_ptag
  (call I.ltag (final ::ᵥ nil)) (HistoryAppend.appendCall I.atag pre (call I.rtag (final ::ᵥ nil)))
 obtain ⟨hneg⟩ := TokenProof.appendPrefix p I (call I.rtag (final ::ᵥ nil))
 exact ⟨Logic.trans _ _ _ hproject (Logic.trans _ _ _ hproj hneg)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.OutputProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.OutputProof
