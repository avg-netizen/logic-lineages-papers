module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTargets
import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTestProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo vectorOne exactEqualityEvaluation)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalControlGraphSupportProof (programRename compositionValue successorValue projectionValue outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast encodeState)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowScalarAlgorithm (canonical)
open NumberedWindowFunctionalGraphTargets (someValue)
open NumberedWindowInternalSparseCanonicalCoordinatesTargets
attribute [local irreducible] programGraph

private theorem evaluated (least : Program 3) (ctx ty k : Nat) :
    evaluate (fixedValue least) (ctx ::ᵥ ty ::ᵥ k ::ᵥ nil) =
    if evaluate least (ctx ::ᵥ ty ::ᵥ k ::ᵥ nil) = k+1 then 1 else 0 := by
  change evaluate equalityTest (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![least,someValue] : Fin 2 → Program 3) i) (ctx ::ᵥ ty ::ᵥ k ::ᵥ nil))) = _
  rw [vectorTwo,exactEqualityEvaluation]
  rfl

theorem calibration : ExactCoordinateCalibration := by
  intro s W least hW hL ctx ty k
  rw [canonicalCoordinates,actualConjunctionEvaluation,evaluated,hW,hL]
  cases hc : unpack ctx with
  | none => simp [packedWindow,packedLeast,hc,encodeState]
  | some g =>
    cases h : NumberedWindowScalarAlgorithm.least s g ty k with
    | none => simp [packedWindow,packedLeast,hc,h,canonical,encodeState]
    | some a =>
      cases hw : NumberedWindowScalarAlgorithm.admitted s g ty k <;> by_cases ha : a = k <;>
        simp [packedWindow,packedLeast,canonical,encodeState,hc,h,hw,ha,beq_eq_decide]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem someGraph (ctx ty k : OTerm α) :
    Nonempty (Derivation body Γ (programGraph someValue (suc k) ![ctx,ty,k])) := by
  apply compositionValue .succ (fun _ : Fin 1 => .projection 2) (suc k) ![ctx,ty,k] ![k] (successorValue ![k])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![ctx,ty,k]

private theorem fixedRead (least : Program 3) (ctx ty k : OTerm α)
    (good : Nonempty (Derivation body Γ (windowAt (fixedValue least) ctx ty k))) :
    Nonempty (Derivation body Γ (programGraph least (suc k) ![ctx,ty,k])) := by
  apply programCases least ![ctx,ty,k] _
  intro β j Δ out keep val
  rw [programRename,sucRelabel,tripleInputsRename]
  rw [tripleInputsRename] at val
  have h := renameInto good j Δ keep
  simp only [windowAt,programRename,sucRelabel,zRelabel,tripleInputsRename] at h
  let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,k.relabel j]
  have observed := compositionRecover equalityTest ![least,someValue] (suc z) xs ![out,suc (k.relabel j)] h
    (fun i => Fin.cases val (Fin.cases (someGraph (ctx.relabel j) (ty.relabel j) (k.relabel j)) (fun e => Fin.elim0 e)) i)
  exact outputTransport least out (suc (k.relabel j)) xs (equalityOfAcceptance _ _ observed) val

theorem openTest : ExactOpenCoordinateTest := by
  intro W least body α Γ ctx ty k
  let xs : Fin 3 → OTerm α := ![ctx,ty,k]
  let A := windowAt (canonicalCoordinates W least) ctx ty k
  let B := windowAt W ctx ty k ⊓ programGraph least (suc k) xs
  have left : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨both⟩ := conjunctionRecover W (fixedValue least) xs ⟨left⟩
  obtain ⟨out⟩ := fixedRead least ctx ty k ⟨Derivation.conjunctionRight both⟩
  have right : Derivation body (B :: Γ) B := Derivation.hypothesis List.mem_cons_self
  have fixed : Nonempty (Derivation body (B :: Γ) (windowAt (fixedValue least) ctx ty k)) := by
    apply compositionValue equalityTest ![least,someValue] (suc z) xs ![suc k,suc k] (equalitySelf (suc k))
    intro i
    exact Fin.cases ⟨Derivation.conjunctionRight right⟩ (Fin.cases (someGraph ctx ty k) (fun e => Fin.elim0 e)) i
  obtain ⟨accepted⟩ := conjunctionAccept W (fixedValue least) xs ⟨Derivation.conjunctionLeft right⟩ fixed
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft both) out)) (Derivation.implicationIntroduction accepted)⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalCoordinatesTestProof
