module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldFuelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldResultEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (emptyUnpack packOfUnpack)
open NumberedWindowInternalSparsePathAdvanceTargets
open NumberedWindowInternalSparsePositiveFoldTargets
open NumberedWindowInternalSparsePositiveFoldFuelProof (fuel optionRound)
open NumberedWindowInternalSparsePositiveFoldResultEvaluationProof (checkValue)

private theorem actualFold (entries : Entries) (s : Settings) (c ty start cert : Nat)
    (g : List Nat) (decoded : unpack c = some g) :
    originalFold entries s c ty start cert =
      (unpack cert).bind (fun hops =>
        hops.foldl (NumberedWindowPositivePathAlgorithm.advance
          (NumberedWindowConcreteCheckers.step entries s g ty) (least s g ty)) (decodeState start)) := by
  have fn (a : Option Nat) (h : Nat) :
      packedOriginalAdvance entries s c ty (encodeState a) h =
        NumberedWindowPositivePathAlgorithm.advance
          (NumberedWindowConcreteCheckers.step entries s g ty) (least s g ty) a h := by
    simp only [packedOriginalAdvance,decoded,Option.bind_eq_bind,Option.bind_some,optionRound]
  simp only [originalFold,fn,Option.bind_eq_bind]

private theorem failContext (entries : Entries) (s : Settings) (c ty start cert : Nat)
    (decoded : unpack c = none) (nonempty : cert ≠ 0) :
    originalFold entries s c ty start cert = none := by
  let fn := fun a h => packedOriginalAdvance entries s c ty (encodeState a) h
  have fnNone (a : Option Nat) (h : Nat) : fn a h = none := by
    simp only [fn,packedOriginalAdvance,decoded,Option.bind_eq_bind,Option.bind_none]
  have dies (hops : List Nat) : hops.foldl fn none = none := by
    induction hops with
    | nil => rfl
    | cons h ls ih => rw [List.foldl_cons,fnNone,ih]
  unfold originalFold
  cases found : unpack cert with
  | none => simp only [found,Option.bind_eq_bind,Option.bind_none]
  | some hops =>
    cases hops with
    | nil => exact False.elim (nonempty (packOfUnpack cert found))
    | cons h hs =>
      simp only [found,Option.bind_eq_bind,Option.bind_some,List.foldl_cons]
      change hs.foldl fn (fn (decodeState start) h) = none
      rw [fnNone,dies]

private theorem originalAccepts (entries : Entries) (s : Settings) (c ty source cert target : Nat) :
    (cert ≠ 0 ∧ originalFold entries s c ty (source+1) cert = some target) ↔
      packedPositive entries s c ty source cert target = true := by
  cases decoded : unpack c with
  | none =>
    have zero : packedPositive entries s c ty source cert target = false := by
      simp [packedPositive,decoded]
    rw [zero]
    constructor
    · rintro ⟨nz,ok⟩
      rw [failContext entries s c ty (source+1) cert decoded nz] at ok
      cases ok
    · intro bad; cases bad
  | some g =>
    rw [actualFold entries s c ty (source+1) cert g decoded]
    cases found : unpack cert with
    | none =>
      simp [packedPositive,decoded,NumberedWindowPositivePathAlgorithm.positive,found]
    | some hops =>
      cases hops with
      | nil =>
        have nilCode : cert = 0 := packOfUnpack cert found
        simp [packedPositive,decoded,NumberedWindowPositivePathAlgorithm.positive,nilCode,emptyUnpack]
      | cons h hs =>
        have nz : cert ≠ 0 := by
          intro nilCode
          subst cert
          rw [emptyUnpack] at found
          cases found
        simp [packedPositive,decoded,NumberedWindowPositivePathAlgorithm.positive,
          NumberedWindowPositivePathAlgorithm.walk,found,decodeState,nz,beq_iff_eq]

theorem composition : FoldComposition := by
  intro entries s raw p advance
  have done := fuel entries s raw p advance
  refine ⟨done, ?_⟩
  intro c ty source cert target
  classical
  rw [checkValue entries s raw p done]
  have acceptEquivalence := originalAccepts entries s c ty source cert target
  by_cases yes : packedPositive entries s c ty source cert target = true
  · rw [if_pos (acceptEquivalence.mpr yes),yes] <;> rfl
  · rw [if_neg (fun h => yes (acceptEquivalence.mp h)),if_neg yes]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldCoreCalibrationProof
