module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeRoot
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeCalls
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof GorbowFormulaSubstitution

def args (tag offset value : Nat) := tag ::ᵥ offset ::ᵥ value ::ᵥ nil
def nums (value : Nat) : List.Vector (Term 0) 1 := Term.numeral value ::ᵥ nil
def calls (tag offset value : Nat) : List.Vector (Term 0) 2 :=
 call (tag+2) (nums value) ::ᵥ call (tag+offset) (nums value) ::ᵥ nil

theorem left (tag offset value : Nat) : evaluate leftCode (args tag offset value) =
 Encodable.encode (GorbowTermPrefixCode.encode (call tag (nums value))) := by
 apply CurrentCompositionProducerProgram.CallEncoding.native target (rawInput ::ᵥ nil) _ tag (nums value)
 · exact NativeValues.tagEval tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact NativeValues.inputEval tag offset value

theorem first (tag offset value : Nat) : evaluate firstCall (args tag offset value) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (tag+2) (nums value))) := by
 apply CurrentCompositionProducerProgram.CallEncoding.native firstTag (rawInput ::ᵥ nil) _ (tag+2) (nums value)
 · exact NativeValues.firstEval tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact NativeValues.inputEval tag offset value

theorem second (tag offset value : Nat) : evaluate secondCall (args tag offset value) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (tag+offset) (nums value))) := by
 apply CurrentCompositionProducerProgram.CallEncoding.native secondTag (rawInput ::ᵥ nil) _ (tag+offset) (nums value)
 · exact NativeValues.secondEval tag offset value
 · intro i
   have hi : i = 0 := Fin.eq_zero i
   subst i
   exact NativeValues.inputEval tag offset value

theorem middle (tag offset value : Nat) : evaluate middleCode (args tag offset value) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (tag+1) (calls tag offset value))) := by
 apply CurrentCompositionProducerProgram.CallEncoding.native projectionTag (firstCall ::ᵥ secondCall ::ᵥ nil) _ (tag+1) (calls tag offset value)
 · exact NativeValues.projectionEval tag offset value
 · intro i
   refine Fin.cases ?_ (fun j => ?_) i
   · exact first tag offset value
   · have hj : j = 0 := Fin.eq_zero j
     subst j
     exact second tag offset value

theorem projectionSeedEval (tag offset value : Nat) : evaluate projectionSeed (args tag offset value) =
 PrescribedRuntimeSpecialization.produce (CorrectedAugmentationErasure.projectionFormula tag)
  (calls tag offset value).get (PrescribedSourceAxiomSpecialization.seed (CorrectedAugmentationErasure.projectionFormula tag)) := by
 have h : ∀ i, evaluate ((firstCall ::ᵥ secondCall ::ᵥ applyOne LiteralNumeralPrefix.numeralCode projectionTag ::ᵥ nil).get i) (args tag offset value) =
  Encodable.encode (GorbowTermPrefixCode.encode (CurrentRecursionBaseProgram.TagSyntax.join (tag+1) (calls tag offset value).get i)) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [CurrentRecursionBaseProgram.TagSyntax.join,Fin.lastCases_last]
    change evaluate (applyOne LiteralNumeralPrefix.numeralCode projectionTag) (args tag offset value) = _
    rw [oneEval,NativeValues.projectionEval,LiteralNumeralPrefix.StatementChecks.exactNative]
  · simp only [CurrentRecursionBaseProgram.TagSyntax.join,Fin.lastCases_castSucc]
    refine Fin.cases ?_ (fun l => ?_) j
    · exact first tag offset value
    · have hl : l = 0 := Fin.eq_zero l
      subst l
      exact second tag offset value
 have hs := CurrentRecursionBaseProgram.SeedNativeProof.seed (args tag offset value) (tag+1) 2 projectionTemplate _ _ h
 rw [SyntaxProof.projection] at hs
 exact hs

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeCalls
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.NativeCalls
