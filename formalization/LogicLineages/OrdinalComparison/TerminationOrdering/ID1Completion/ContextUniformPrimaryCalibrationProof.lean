module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedUniformPackedDecoding
open ContextUniformPrimary

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

theorem actualRawClassCodesCalibration : ContextUniformPrimaryTargets.ActualRawClassCodesCalibration := by
  intro n arity symbols S Gamma q
  unfold classCodes NumberedAuxiliaryEnumeration.classCodes
  simp only [packedCode]
  rw [NumberedSyntaxBoundsPrimrecProof.termBoundsCalibration (Fin n) arity Gamma q.1 q.2]

theorem candidatesCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    candidates arity symbols S Gamma (packedCode q) =
      (NumberedAuxiliaryDecoding.classCandidates symbols S q).map packedCode := by
  unfold candidates NumberedAuxiliaryDecoding.classCandidates
  rw [actualRawClassCodesCalibration]
  generalize NumberedAuxiliaryEnumeration.classCodes symbols S q = cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.filterMap_cons,List.filterMap_cons,NumberedUniformPackedDecodingProof.rawStructuralCalibration]
    cases hd : NumberedAuxiliaryDecoding.decodePacked arity Gamma c <;> simp [hd,ih]

theorem verticesCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    vertices arity symbols S Gamma (packedCode q) =
      (NumberedPrimaryClassPrimrec.vertexList symbols S q).map packedCode := by
  rw [vertices,NumberedPrimaryClassPrimrec.vertexList,candidatesCalibration,List.map_cons]

theorem anyExchangeCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (reached : List (Packed (Fin n) arity Gamma)) (r : Packed (Fin n) arity Gamma) :
    (reached.map packedCode).any (fun a =>
      NumberedExchangeCode.packedCodeExchange arity symbols S a (packedCode r)) =
      reached.any (fun a => NumberedExchangeNeighborhood.exchangeTest symbols S a r) := by
  induction reached with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons,List.any_cons]
    rw [NumberedExchangePrimrecProof.packedCalibration (Fin n) inferInstance arity Gamma symbols S a r,ih]

theorem stepCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (pool reached : List (Packed (Fin n) arity Gamma)) :
    step arity symbols S (pool.map packedCode) (reached.map packedCode) =
      (NumberedPrimaryClassPrimrec.step symbols S pool reached).map packedCode := by
  unfold step NumberedPrimaryClassPrimrec.step
  rw [List.map_append]
  congr 1
  induction pool with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.map_cons,List.filter_cons,anyExchangeCalibration]
    cases h : reached.any (fun a => NumberedExchangeNeighborhood.exchangeTest symbols S a r) <;>
      try simp only [h,List.map_cons]
    · exact ih
    · exact congrArg (List.cons (packedCode r)) ih

theorem reachableCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) (fuel : Nat) :
    reachable arity symbols S Gamma (packedCode q) fuel =
      (NumberedPrimaryClassPrimrec.reachableList symbols S q fuel).map packedCode := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [reachable,NumberedPrimaryClassPrimrec.reachableList,Function.iterate_succ_apply'] at ih ⊢
    rw [ih,verticesCalibration,stepCalibration]

theorem actualRawPrimaryListCalibration : ContextUniformPrimaryTargets.ActualRawPrimaryListCalibration := by
  intro n arity symbols S Gamma q
  unfold primaryList NumberedPrimaryClassPrimrec.primaryList
  rw [verticesCalibration,List.length_map,reachableCalibration]

theorem actualRawPrimaryTestCalibration : ContextUniformPrimaryTargets.ActualRawPrimaryTestCalibration := by
  intro n arity symbols S Gamma q r
  rw [primaryTest,actualRawPrimaryListCalibration,
    ← NumberedPrimaryClassPrimrecSupportProof.primaryTestCalibration symbols S q r]
  rw [decide_eq_decide]
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    have har := NumberedAuxiliaryCodingProof.packedCodeInjective (Fin n) arity Gamma he
    cases har
    exact ha
  · intro h
    exact List.mem_map.mpr ⟨r,h,rfl⟩

theorem classNumberTestCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) (value : Nat) :
    classNumberTest arity symbols S Gamma (packedCode q) value =
      NumberedRepresentativePrimrec.classNumberTest symbols S q value := by
  unfold classNumberTest NumberedRepresentativePrimrec.classNumberTest
  rw [NumberedUniformPackedDecodingProof.rawPackedCalibration]
  cases hd : NumberedNumericDecoding.decodePackedNumber n arity Gamma value with
  | none => rfl
  | some r =>
    simpa only [Option.map_some,Option.any_some] using
      actualRawPrimaryTestCalibration n arity symbols S Gamma q r

theorem boundedRepresentativeCalibration {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    representative arity symbols S Gamma (packedCode q) =
      NumberedRepresentativePrimrec.boundedRepresentative symbols S q := by
  unfold representative NumberedRepresentativePrimrec.boundedRepresentative
  have he : packedNumber (packedCode q) = NumberedLeastCodeRepresentative.packedNumber q := rfl
  rw [he]
  congr 1
  funext value
  exact classNumberTestCalibration arity symbols S Gamma q value

theorem actualRawRepresentativeCalibration : ContextUniformPrimaryTargets.ActualRawRepresentativeCalibration := by
  intro n arity symbols S Gamma q
  rw [boundedRepresentativeCalibration]
  exact NumberedRepresentativePrimrecSupportProof.boundedRepresentativeCalibration n arity Gamma symbols S q

theorem actualUniformCanonicalCalibration : ContextUniformPrimaryTargets.ActualUniformCanonicalCalibration := by
  intro n arity symbols S Gamma value
  unfold canonicalCarrier NumberedNumericCarrier.canonicalCarrierTest
  rw [NumberedUniformPackedDecodingProof.rawUniverseCalibration]
  cases hd : NumberedNumericCarrier.decodeUniverse n arity symbols S Gamma value with
  | none => rfl
  | some q =>
    simp only [Option.map_some,Option.any_some]
    rw [actualRawRepresentativeCalibration n arity symbols S Gamma q]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimaryCalibrationProof
