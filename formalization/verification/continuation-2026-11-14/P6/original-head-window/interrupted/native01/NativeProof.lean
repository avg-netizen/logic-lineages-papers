module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadResult.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public import Mathlib.Data.List.GetD
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedAuxiliaryDecoding NumberedFiniteUniverse Source.SourceMarkedSyntax
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open TwoSol20261113.CalibratedPrimary.Membership
open OriginalHeadResult.NativeProof (arrowEvaluation)
open OriginalHeadEncodingBridge.NativeProof (projectionOne typeEncoding)

theorem projectionValue {n : Nat} (i : Fin n) (v : List.Vector Nat n) : evaluate (.projection i) v = v.get i := rfl

theorem arityValue (n : Nat) (arity : Fin n → Nat) (payload symbols types : Nat) :
    evaluate (arityAt n arity) (payload ::ᵥ symbols ::ᵥ types ::ᵥ nil) = (List.ofFn arity).getD payload 0 := by
  change evaluate InternalRawListRecursion.lookup (ofFn ![payload,NumberedMultisetNumeric.numbersNumber (List.ofFn arity)]) = _
  exact ExchangeAnswerSlots.NativeProof.lookupEncoded payload (List.ofFn arity)

theorem nativeArity : Targets.NativeArity := by
  intro n arity s symbols types
  rw [arityValue,List.getD_eq_getElem (by simpa using s.isLt)]
  simp

theorem containsValue (xs : List Nat) (needle : Nat) :
    evaluate contains (ofFn ![numbersNumber xs,needle]) = (decide (needle ∈ xs)).toNat := by
  have h := TwoSol20261113.CalibratedPrimary.MembershipNativeProof.actualContainsNative (numbersNumber xs) needle
  simpa only [numbersRoundTrip,Option.getD_some] using h

theorem typeMemberValue (p : Program 3) (payload symbols : Nat) (types : List Ty) :
    evaluate (typeMember p) (payload ::ᵥ symbols ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) =
      (decide (evaluate p (payload ::ᵥ symbols ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) ∈ types.map typeNumber)).toNat := by
  rw [typeMember,binaryCompositionEvaluation]
  exact containsValue _ _

theorem typeMem (tau : Ty) (types : List Ty) : typeNumber tau ∈ types.map typeNumber ↔ tau ∈ types := by
  constructor
  · intro h
    obtain ⟨t,ht,he⟩ := List.mem_map.mp h
    exact NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective he ▸ ht
  · exact List.mem_map_of_mem

theorem symbolMem (n : Nat) (s : Fin n) (symbols : List (Fin n)) : s.val ∈ symbols.map Fin.val ↔ s ∈ symbols := by
  constructor
  · intro h
    obtain ⟨t,ht,he⟩ := List.mem_map.mp h
    exact Fin.ext he ▸ ht
  · exact List.mem_map_of_mem

theorem chooseValue (tag : Nat) (yes no : Program 3) (raw symbols types : Nat) :
    evaluate (choose tag yes no) (raw ::ᵥ symbols ::ᵥ types ::ᵥ nil) =
      if (Nat.unpair raw).1 = tag then evaluate yes (raw ::ᵥ symbols ::ᵥ types ::ᵥ nil)
      else evaluate no (raw ::ᵥ symbols ::ᵥ types ::ᵥ nil) := by
  simp only [choose,evalBranch,sameOfEvaluation,leftOfEvaluation,constantEvaluation,projectionValue]
  change (if (if (Nat.unpair raw).1 = tag then 1 else 0) = 0 then _ else _) = _
  split_ifs <;> simp_all

theorem payloadValue (n : Nat) (arity : Fin n → Nat) (tag raw symbols types : Nat) :
    evaluate (atPayload n arity tag) (raw ::ᵥ symbols ::ᵥ types ::ᵥ nil) =
      evaluate (branchWindow n arity tag) ((Nat.unpair raw).2 ::ᵥ symbols ::ᵥ types ::ᵥ nil) := by
  rw [atPayload,ternaryCompositionEvaluation,rightOfEvaluation]
  rfl

theorem nativeWindow : Targets.NativeWindow := by
  intro n arity symbols types head
  cases head <;>
    simp [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      applicationArguments,rankedArguments,actualConjunctionEvaluation,evalBranch,
      typeMemberValue,constantEvaluation,unaryCompositionEvaluation,
      OriginalHeadResult.branchResult,arrowEvaluation,projectionOne,projectionValue,
      succOfEvaluation,leftOfEvaluation,rightEvaluation,binaryCompositionEvaluation,containsValue,
      arityValue,List.getD_eq_getElem,decodeHead,HeadInWindow,RankedCovered,headResult,headArguments,
      Ty.caseType,Ty.recType,typeNumber,typeMem,symbolMem,Nat.add_comm]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
