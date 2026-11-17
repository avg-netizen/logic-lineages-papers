module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SyntaxProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeEvaluation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeValues
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof

theorem tagEval (tag offset value : Nat) : evaluate target (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) = tag := rfl
theorem projectionEval (tag offset value : Nat) : evaluate projectionTag (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) = tag+1 := by
 rw [projectionTag,oneEval,tagEval]
 rfl
theorem firstEval (tag offset value : Nat) : evaluate firstTag (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) = tag+2 := by
 exact CurrentRecursionStepProgram.NativeEvaluation.shiftEval 2 target _
theorem secondEval (tag offset value : Nat) : evaluate secondTag (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) = tag+offset := by
 rw [secondTag,twoEval,tagEval]
 change evaluate HistoryCodec.add (tag ::ᵥ offset ::ᵥ nil) = tag+offset
 simpa only [Nat.add_comm] using HistoryCodec.NativeProof.evaluateAdd tag offset
theorem inputEval (tag offset value : Nat) : evaluate rawInput (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) =
 Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral value : Term 0)) := by
 rw [rawInput,oneEval]
 exact LiteralNumeralPrefix.StatementChecks.exactNative value

theorem tagsEval (tag offset value : Nat) (i : Fin 4) :
 evaluate (rawTags.get i) (tag ::ᵥ offset ::ᵥ value ::ᵥ nil) =
 Encodable.encode (GorbowTermPrefixCode.encode ((SyntaxProof.addresses tag offset).get i)) := by
 simp only [rawTags,List.Vector.get_map]
 refine Fin.cases ?_ (fun i => ?_) i
 · rw [List.Vector.get_cons_zero,oneEval,tagEval,LiteralNumeralPrefix.StatementChecks.exactNative]; rfl
 · refine Fin.cases ?_ (fun i => ?_) i
   · rw [List.Vector.get_cons_succ,List.Vector.get_cons_zero,oneEval,projectionEval,LiteralNumeralPrefix.StatementChecks.exactNative]; rfl
   · refine Fin.cases ?_ (fun i => ?_) i
     · simp only [List.Vector.get_cons_succ,List.Vector.get_cons_zero]
       rw [oneEval,firstEval,LiteralNumeralPrefix.StatementChecks.exactNative]; rfl
     · have hi : i = 0 := Fin.eq_zero i
       subst i
       simp only [List.Vector.get_cons_succ,List.Vector.get_cons_zero]
       rw [oneEval,secondEval,LiteralNumeralPrefix.StatementChecks.exactNative]; rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeValues
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeValues
