import LogicLineages.PersistentMarking.NumberedWindowOuterShapeTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticNodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowOuterShapeProof
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPrimary
open NumberedWindowOuterShape NumberedWindowOuterShapeTargets
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticScalarChecks
open NumberedWindowArithmeticAddressAlgorithmChecks NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticAllContextTargets NumberedWindowArithmeticLeastClass
open NumberedWindowTypingBitsChecks NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode
open NumberedWindowArithmeticFieldAlgorithmChecks NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticAddressAlgorithmTargets (address)
open NumberedWindowFieldAlgorithm (unpackNode)

private theorem primaryTag {S K C τ Q R} (h : Primary S K C τ Q R) :
    literalTag Q = literalTag R := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | symm _ eq => exact eq.symm
  | trans _ _ left right => exact left.trans right
  | _ => first | rfl | trivial

private def classTag {S K C τ} : Class S K C τ → Nat :=
  Quot.lift (fun Q : WindowCarrier S K C τ => literalTag Q.val) (fun _ _ h => primaryTag h)

private theorem tagOfRepresentatives {S K C τ} (Q : WindowCarrier S K C τ)
    {q : Class S K C τ} (e : classOf Q = q) : RepresentsTag q (literalTag Q.val) := by
  intro R hR
  exact congrArg classTag (hR.trans e.symm)

private theorem shapeOfEncoded (Q : NTerm) :
    (unpackNode (encodeTerm Q)).map Prod.fst = some (literalTag Q) := by
  cases Q <;> simp [encodeTerm,literalTag,← exact_ExactTaggedNodeCodec.2,nodeRound]

private theorem shapeOnAddress (S : Signature) (K : List Ty) {n : Nat} {a : ClassAddress}
    (readAddress : decodeAddress n = some a) :
    outerShape (fixed S K) n =
      if canonicalBit S K a then (unpackNode a.least).map Prod.fst else none := by
  have h := congrFun (exact_ScalarAddress S K) n
  have check : NumberedWindowScalarAlgorithm.canonical (fixed S K) (address a) =
      canonicalBit S K a := by
    simpa [NumberedWindowScalarAlgorithm.scalar,exact_ExactAddressView n,readAddress,addressBit] using h
  simp only [outerShape,exact_ExactAddressView n,readAddress,Option.map_some,
    Option.bind_eq_bind,Option.bind_some,check] <;> rfl

private theorem atActualCode {S : Signature} {K Γ : List Ty} {τ : Ty} {i : Nat}
    (hk : DecisionSourceUniverse.Closed K) {q : Class S K (finiteC Γ) τ}
    (hq : ActualCodeAt S K Γ τ i q) :
    ∃ tag, outerShape (fixed S K) (encodeAddress ⟨Γ,τ,i⟩) = some tag ∧ RepresentsTag q tag := by
  have valid :=
    (NumberedWindowArithmeticAllContextAdmittedProof.canonical S K ⟨Γ,τ,i⟩ hk).mpr ⟨q,hq⟩
  have number := shapeOnAddress S K (round ⟨Γ,τ,i⟩)
  simp [valid] at number
  cases ht : decodeTerm i with
  | none => simp [canonicalBit,ht] at valid
  | some term =>
    simp only [canonicalBit,ht,Bool.and_eq_true,decide_eq_true_eq] at valid
    let Q : WindowCarrier S K (finiteC Γ) τ :=
      ⟨term,(exact_FiniteWindowBit S K Γ τ term).mp valid.1⟩
    have codeQ : ActualCodeAt S K Γ τ i (classOf Q) := ⟨Q,rfl,valid.2⟩
    have same := sameClass hk codeQ hq
    have equation : encodeTerm term = i := (exact_TermCodec.1 i term).mp ht
    refine ⟨literalTag term,?_,tagOfRepresentatives Q same⟩
    rw [number]
    change (unpackNode i).map Prod.fst = some (literalTag term)
    rw [← equation]
    exact shapeOfEncoded term

theorem shape : ExactOuterShape := by
  intro S K hk n tag
  constructor
  · intro found
    cases readAddress : decodeAddress n with
    | none => simp [outerShape,exact_ExactAddressView n,readAddress] at found
    | some a =>
      rcases a with ⟨Γ,τ,i⟩
      by_cases valid : canonicalBit S K ⟨Γ,τ,i⟩ = true
      · obtain ⟨q,hq⟩ := (NumberedWindowArithmeticAllContextAdmittedProof.canonical
          S K ⟨Γ,τ,i⟩ hk).mp valid
        have code := read readAddress
        obtain ⟨k,checked,reps⟩ := atActualCode hk hq
        rw [code,found] at checked
        have agree := Option.some.inj checked
        subst k
        exact ⟨Γ,τ,i,q,code,hq,reps⟩
      · rw [shapeOnAddress S K readAddress] at found
        simp [valid] at found
  · rintro ⟨Γ,τ,i,q,addressCode,hq,reps⟩
    obtain ⟨k,yes,actual⟩ := atActualCode hk hq
    obtain ⟨Q,same,_⟩ := hq
    have agreement : k = tag := (actual Q same).symm.trans (reps Q same)
    rw [← addressCode,yes,agreement]

theorem reject : ExactOuterShapeReject := by
  intro S K hk n
  constructor
  · rintro none ⟨Γ,τ,i,q,addressCode,hq⟩
    obtain ⟨tag,h,_⟩ := atActualCode hk hq
    rw [addressCode,none] at h
    cases h
  · intro unadmitted
    cases h : outerShape (fixed S K) n with
    | none => rfl
    | some tag =>
      obtain ⟨Γ,τ,i,q,addressCode,hq,_⟩ := (shape S K hk n tag).mp h
      exact (unadmitted ⟨Γ,τ,i,q,addressCode,hq⟩).elim

end LogicLineages.PersistentMarking.NumberedWindowOuterShapeProof
