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
  rw [arityAt,binaryCompositionEvaluation,constantEvaluation]
  change evaluate InternalRawListRecursion.lookup (ofFn ![payload,NumberedMultisetNumeric.numbersNumber (List.ofFn arity)]) = _
  exact ExchangeAnswerSlots.NativeProof.lookupEncoded payload (List.ofFn arity)

theorem nativeArity : Targets.NativeArity := by
  intro n arity s symbols types
  change evaluate (arityAt n arity) (s.val ::ᵥ symbols ::ᵥ types ::ᵥ nil) = _
  rw [arityValue,List.getD_eq_getElem (List.ofFn arity) 0 (by simpa using s.isLt)]
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

theorem conjunctionValue {k : Nat} (p q : Program k) (v : List.Vector Nat k) :
    evaluate (InternalAcceptance.conjunction p q) v =
      if evaluate p v = 1 ∧ evaluate q v = 1 then 1 else 0 :=
  actualConjunctionEvaluation k p q v

theorem getZero3 (a b c : Nat) : (a ::ᵥ b ::ᵥ c ::ᵥ nil).get (0 : Fin 3) = a := rfl
theorem getOne3 (a b c : Nat) : (a ::ᵥ b ::ᵥ c ::ᵥ nil).get (1 : Fin 3) = b := rfl
theorem getZero1 (a : Nat) : (ofFn ![a]).get (0 : Fin 1) = a := rfl

theorem nativeWindow : Targets.NativeWindow := by
  intro n arity symbols types head
  change evaluate (window n arity)
    (headNumber head ::ᵥ numbersNumber (symbols.map Fin.val) ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) = _
  cases head with
  | zero =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (0 : Nat) ≠ 1 from by decide), (show (0 : Nat) ≠ 2 from by decide), (show (0 : Nat) ≠ 3 from by decide), (show (0 : Nat) ≠ 4 from by decide), (show (0 : Nat) ≠ 5 from by decide),ite_false,ite_true,typeMemberValue,unaryCompositionEvaluation,
      OriginalHeadResult.branchResult,constantEvaluation]
    change (decide (typeNumber Ty.ground ∈ types.map typeNumber)).toNat = _
    simp only [typeMem]
    simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments]
  | succ =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (1 : Nat) ≠ 0 from by decide), (show (1 : Nat) ≠ 2 from by decide), (show (1 : Nat) ≠ 3 from by decide), (show (1 : Nat) ≠ 4 from by decide), (show (1 : Nat) ≠ 5 from by decide),ite_false,ite_true,typeMemberValue,unaryCompositionEvaluation,
      OriginalHeadResult.branchResult,arrowEvaluation,constantEvaluation]
    change (decide (typeNumber (Ty.arrow .ground .ground) ∈ types.map typeNumber)).toNat = _
    simp only [typeMem]
    simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments]
  | cases tau =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (2 : Nat) ≠ 0 from by decide), (show (2 : Nat) ≠ 1 from by decide), (show (2 : Nat) ≠ 3 from by decide), (show (2 : Nat) ≠ 4 from by decide), (show (2 : Nat) ≠ 5 from by decide),ite_false,ite_true,typeMemberValue,unaryCompositionEvaluation,
      OriginalHeadResult.branchResult,arrowEvaluation,constantEvaluation,projectionOne]
    change (decide (typeNumber tau.caseType ∈ types.map typeNumber)).toNat = _
    simp only [typeMem]
    simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments]
  | recursor tau =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (3 : Nat) ≠ 0 from by decide), (show (3 : Nat) ≠ 1 from by decide), (show (3 : Nat) ≠ 2 from by decide), (show (3 : Nat) ≠ 4 from by decide), (show (3 : Nat) ≠ 5 from by decide),ite_false,ite_true,typeMemberValue,unaryCompositionEvaluation,
      OriginalHeadResult.branchResult,arrowEvaluation,constantEvaluation,projectionOne]
    change (decide (typeNumber tau.recType ∈ types.map typeNumber)).toNat = _
    simp only [typeMem]
    simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments]
  | application sigma tau =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (4 : Nat) ≠ 0 from by decide), (show (4 : Nat) ≠ 1 from by decide), (show (4 : Nat) ≠ 2 from by decide), (show (4 : Nat) ≠ 3 from by decide), (show (4 : Nat) ≠ 5 from by decide),ite_false,ite_true,applicationArguments,conjunctionValue,
      typeMemberValue,unaryCompositionEvaluation,OriginalHeadResult.branchResult,
      rightEvaluation,succOfEvaluation,leftOfEvaluation,projectionValue]
    simp only [getZero3,getZero1,Nat.unpair_pair,Nat.add_comm]
    change (if (decide (typeNumber tau ∈ types.map typeNumber)).toNat = 1 ∧
      (if (decide (typeNumber (Ty.arrow sigma tau) ∈ types.map typeNumber)).toNat = 1 ∧
        (decide (typeNumber sigma ∈ types.map typeNumber)).toNat = 1 then 1 else 0) = 1 then 1 else 0) = _
    simp only [typeMem]
    by_cases ht : tau ∈ types <;> by_cases ha : Ty.arrow sigma tau ∈ types <;> by_cases hs : sigma ∈ types <;>
      simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments,ht,ha,hs]
  | ranked symbol =>
    simp only [window,chooseValue,headNumber,Nat.unpair_pair,payloadValue,branchWindow,
      (show (5 : Nat) ≠ 0 from by decide), (show (5 : Nat) ≠ 1 from by decide), (show (5 : Nat) ≠ 2 from by decide), (show (5 : Nat) ≠ 3 from by decide), (show (5 : Nat) ≠ 4 from by decide),ite_false,ite_true,conjunctionValue,rankedArguments,evalBranch,
      typeMemberValue,unaryCompositionEvaluation,OriginalHeadResult.branchResult,
      constantEvaluation,binaryCompositionEvaluation,containsValue]
    have har := nativeArity n arity symbol (numbersNumber (symbols.map Fin.val)) (numbersNumber (types.map typeNumber))
    change evaluate (arityAt n arity) (symbol.val ::ᵥ numbersNumber (symbols.map Fin.val) ::ᵥ numbersNumber (types.map typeNumber) ::ᵥ nil) = _ at har
    rw [har]
    simp only [projectionValue,getZero3,getOne3,containsValue]
    change (if (decide (symbol.val ∈ symbols.map Fin.val)).toNat = 1 ∧
      (if (decide (typeNumber Ty.ground ∈ types.map typeNumber)).toNat = 1 ∧
        (if arity symbol = 0 then 1 else (decide (typeNumber Ty.ground ∈ types.map typeNumber)).toNat) = 1 then 1 else 0) = 1 then 1 else 0) = _
    simp only [symbolMem,typeMem]
    by_cases hs : symbol ∈ symbols <;> by_cases hg : Ty.ground ∈ types <;> by_cases hz : arity symbol = 0 <;>
      simp [HeadInWindow,RankedCovered,decodeHead,headResult,headArguments,hs,hg,hz]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.NativeProof
