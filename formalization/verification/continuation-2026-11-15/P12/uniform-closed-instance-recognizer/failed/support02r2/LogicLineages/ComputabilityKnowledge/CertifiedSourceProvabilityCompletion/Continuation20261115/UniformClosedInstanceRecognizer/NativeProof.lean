module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeFoldProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof NativeFoldProof
/-- Runtime formula code remains data; only the original closed replacement
guard is needed to calibrate the actual emitter/fold. -/
theorem rawFoldAt (formula replacement : List Nat)
 (hr : GorbowSyntaxValidation.validTerm 0 replacement = true) :
 evaluate rawFold (Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil) =
 Encodable.encode (formula.foldl (GorbowSubstitutionCode.subStep 1 0 [replacement])
  ((some [(1,1)],[]) : GorbowSubstitutionCode.OutputState)) := by
 let v := Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil
 let g : Fin 3 → Program 2 := fun i => ((.projection 0) ::ᵥ initialState ::ᵥ (.projection 1) ::ᵥ nil).get i
 have hargs : List.Vector.ofFn (fun i => evaluate (g i) v) =
  (Encodable.encode formula ::ᵥ Encodable.encode ((some [(1,1)],[]) : GorbowSubstitutionCode.OutputState) ::ᵥ
   Encodable.encode replacement ::ᵥ nil) := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero =>
     change evaluate initialState v = Encodable.encode ((some [(1,1)],[]) : GorbowSubstitutionCode.OutputState)
     exact initialAt (Encodable.encode formula) (Encodable.encode replacement)
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i
 change evaluate UniformClosedSubstitutionRawFold.foldCode (List.Vector.ofFn (fun i => evaluate (g i) v)) = _
 rw [hargs]
 exact foldAt ((some [(1,1)],[]) : GorbowSubstitutionCode.OutputState) formula replacement hr
theorem outputAt (formula replacement : List Nat)
 (hr : GorbowSyntaxValidation.validTerm 0 replacement = true) :
 evaluate outputCode (Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil) =
 Encodable.encode (GorbowSubstitutionCode.subRaw 1 1 0 [replacement] formula) := by
 rw [outputCode,oneEval,rawFoldAt formula replacement hr,HistoryDecoder.NativeProof.evaluateDecoder]
 simp only [HistoryDispatcher.NativeProof.encodeProd,HistoryDecoder.NativeProof.coordinate,ite_true,Nat.unpair_pair]
 rfl
theorem exactOriginalInstance : Targets.ExactOriginalInstance := by
 intro formula replacement
 simp only [instanceCode,chooseEval,twoEval,formulaGuard,termGuard,oneEval,constantEval,
  projectionEval,get2_0,get2_1,LiteralSyntaxValidator.NativeProof.formulaEncoded,
  TwoSol20261113.ReflexivityRecognizer.NativeProof.nativeTerm,equalEval]
 by_cases hf : GorbowSyntaxValidation.validFormula 1 formula = true
 · by_cases hr : GorbowSyntaxValidation.validTerm 0 replacement = true
   · simp only [hf,hr,HistoryDispatcher.truth,ite_true,Nat.one_ne_zero,ite_false]
     change (evaluate outputCode (Encodable.encode formula ::ᵥ Encodable.encode replacement ::ᵥ nil)).succ = _
     rw [outputAt formula replacement hr]
     simp [GorbowInstanceCode.instanceCode,GorbowInstanceCode.variableDictionary,
      GorbowSubstitutionCode.substituteFormulaCode,GorbowLiftedDictionary.dictionaryValid,hf,hr]
   · have hr0 : GorbowSyntaxValidation.validTerm 0 replacement = false := Bool.eq_false_iff.mpr hr
     simp [hf,hr0,HistoryDispatcher.truth,GorbowInstanceCode.instanceCode,GorbowInstanceCode.variableDictionary,
      GorbowSubstitutionCode.substituteFormulaCode,GorbowLiftedDictionary.dictionaryValid]
 · have hf0 : GorbowSyntaxValidation.validFormula 1 formula = false := Bool.eq_false_iff.mpr hf
   simp [hf0,HistoryDispatcher.truth,GorbowInstanceCode.instanceCode,GorbowInstanceCode.variableDictionary,
    GorbowSubstitutionCode.substituteFormulaCode,GorbowLiftedDictionary.dictionaryValid]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeProof
