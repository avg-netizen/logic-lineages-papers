module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
open Source NumberedRewriteReduction NumberedAuxiliaryDecoding NumberedAuxiliaryEnumeration
open NumberedFinitePrimaryClass NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open InternalRepresentativeTag InternalQuotientEdgeChecker InternalOriginalStepGuard
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

 theorem candidateType {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q r : Packed (Fin n) arity Gamma)
    (hr : r ∈ classCandidates symbols S q) : r.1 = q.1 := by
  obtain ⟨c,hc,hd⟩ := List.mem_filterMap.mp hr
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hc
  subst c
  unfold decodePacked at hd
  cases hx : decodeTerm arity Gamma q.1 a with
  | none => simp [hx] at hd
  | some t =>
    have he : (⟨q.1,t⟩ : Packed (Fin n) arity Gamma) = r := by
      simpa only [hx,Option.map_some,Option.some.injEq] using hd
    simpa only using congrArg (fun p : Packed (Fin n) arity Gamma => p.1) he.symm

 theorem primaryClassType {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (symbols : List (Fin n)) (S : List Ty) (q r : Packed (Fin n) arity Gamma)
    (hr : r ∈ primaryClass symbols S q) : r.1 = q.1 := by
  have hv := NumberedFinitePrimaryClassProof.reachableBound (Fin n) inferInstance
    arity symbols S Gamma q (vertices symbols S q).card hr
  rcases Finset.mem_insert.mp hv with he | hc
  · exact congrArg Sigma.fst he
  · exact candidateType symbols S q r (List.mem_toFinset.mp hc)

 theorem actualOriginalRepresentativeOuterType :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeOuterType := by
  intro n arity symbols S Gamma q
  have hm := Finset.min'_mem (classNumbers symbols S q) (classNumbersNonempty symbols S q)
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hm
  change (Nat.unpair (representativeCode symbols S q)).1 = _
  change packedNumber r = representativeCode symbols S q at he
  rw [← he]
  simp only [packedNumber,Nat.unpair_pair]
  exact congrArg typeNumber (primaryClassType symbols S q r hr)

 theorem representativeEvaluation (valid oldRepresentative : Program 1) (v : List.Vector Nat 1) :
    evaluate (representative valid oldRepresentative) v =
      if evaluate valid v = 1 then
        Nat.pair (Nat.unpair (v.get 0)).1 (Nat.unpair (evaluate oldRepresentative v)).2
      else 0 := by
  rw [representative,evalBranch,evalNormalize,pairOfEvaluation,leftEvaluation,rightOfEvaluation]
  change (if (if evaluate valid v = 1 then 1 else 0) = 0 then 0 else _) = _
  by_cases h : evaluate valid v = 1 <;> simp [h]

 theorem repackRepresentative (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (raw : Nat) (q : Packed (Fin n) arity Gamma)
    (h : decodePackedNumber n arity Gamma raw = some q) :
    Nat.pair (Nat.unpair raw).1 (Nat.unpair (representativeCode symbols S q)).2 =
      representativeCode symbols S q := by
  have hs := NumberedNumericDecodingProof.packedNumericSound n arity Gamma raw q h
  have ht := actualOriginalRepresentativeOuterType n arity symbols S Gamma q
  rw [← hs]
  simp only [packedNumber,Nat.unpair_pair]
  rw [← ht]
  exact Nat.pair_unpair _

 theorem actualOriginalRepresentativeWrapperCalibration :
    InternalRepresentativeTagTargets.ActualOriginalRepresentativeWrapperCalibration := by
  intro n arity symbols S Gamma table validity old hv ho
  refine ⟨ho.1,?_,?_⟩
  · intro v
    change evaluate (representative validity.sourceValid old.sourceRepresentative) v = _
    rw [representativeEvaluation,hv.1,ho.2.1]
    cases hd : decodeUniverse n arity symbols S Gamma (v.get 0) with
    | none =>
      simp only [sourceValidityValue,rawCarrierTest,sourceRepresentativeValue,hd,
        Option.isSome_none,Bool.toNat_false,Nat.zero_ne_one,ite_false]
    | some q =>
      simp only [sourceValidityValue,rawCarrierTest,sourceRepresentativeValue,hd,
        Option.isSome_some,Bool.toNat_true,ite_true]
      exact repackRepresentative n arity symbols S Gamma (v.get 0) q
        (Option.filter_eq_some_iff.mp hd).1
  · intro v
    change evaluate (representative validity.targetValid old.targetRepresentative) v = _
    rw [representativeEvaluation,hv.2,ho.2.2]
    cases hd : decodePackedNumber n arity Gamma (v.get 0) with
    | none =>
      simp only [targetValidityValue,targetRepresentativeValue,hd,
        Option.isSome_none,Bool.toNat_false,Nat.zero_ne_one,ite_false]
    | some q =>
      simp only [targetValidityValue,targetRepresentativeValue,hd,
        Option.isSome_some,Bool.toNat_true,ite_true]
      exact repackRepresentative n arity symbols S Gamma (v.get 0) q hd

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagEvaluationProof
