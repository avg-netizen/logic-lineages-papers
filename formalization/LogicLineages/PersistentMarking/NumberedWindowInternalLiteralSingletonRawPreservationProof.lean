module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonRawCodecProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWindowSubstitutionChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonChecks
import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonRawPreservationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticTermCode (encodeTerm decodeTerm)
open NumberedWindowArithmeticTermCodeChecks (exact_TermCodec)
open NumberedWindowArithmeticSingletonChecks (exact_ExactSingletonOutput)
open NumberedWindowExternalWindowSubstitutionTargets (HasBottomValue)
open NumberedWindowExternalWindowSubstitutionChecks (exact_SubstitutionWindowStep exact_FreeSubstitutionWindowStep)
open NumberedWindowPreservationBoundProof (Compatible one)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration)
open NumberedWindowInternalLiteralSingletonDepthNumericProof
open NumberedWindowInternalLiteralSingletonRawCodecProof

attribute [local irreducible] fixed

theorem exact_CheckedSingletonInstanceCode (U : Program 3) (fit : DepthInstanceFit U)
    (a q : NTerm) (depth : Nat) :
    evaluate U (encodeTerm a ::ᵥ depth ::ᵥ encodeTerm q ::ᵥ nil) =
      encodeTerm (substitute (.cons a .nil) depth q) + 1 := by
  rw [fit,depthInstanceValue,exact_ExactSingletonOutput,exact_TermCodec.2.1 a,exact_TermCodec.2.1 q]
  rfl

/-- A supplied original certificate remains a real accepted raw
certificate on the exact compiled singleton images, or both images
are identical and the single replacement was bottom. This is numeric
calibration of the real checkers at finite typed contexts, not yet an
open-arithmetic proof of naturality. -/
theorem exact_CheckedSingletonRawPreservation (S : Spine.Signature) (K G H : List Ty) (T : Ty)
    (U : Program 3) (p : Program 5) (uFit : DepthInstanceFit U)
    (pFit : ActualRawCalibration S.entries (fixed S K) p)
    (closed : DecisionSourceUniverse.Closed K) (a q r : NTerm) (depth cert : Nat)
    (compatible : Compatible S K (.cons a .nil) depth
      (Spine.BoundContext.«prefix» G Spine.EmptyContext) (Spine.BoundContext.«prefix» H Spine.EmptyContext))
    (accepted : evaluate p (canonicalTape G T (encodeTerm q) cert (encodeTerm r)) = 1) :
    ∃ q' r', evaluate U (encodeTerm a ::ᵥ depth ::ᵥ encodeTerm q ::ᵥ nil) = q' + 1 ∧
      evaluate U (encodeTerm a ::ᵥ depth ::ᵥ encodeTerm r ::ᵥ nil) = r' + 1 ∧
      ((∃ after, evaluate p (canonicalTape H T q' after r') = 1) ∨
        (q' = r' ∧ ∃ σ, a = NTerm.bottom σ)) := by
  let x := substitute (.cons a .nil) depth q
  let y := substitute (.cons a .nil) depth r
  refine ⟨encodeTerm x,encodeTerm y,exact_CheckedSingletonInstanceCode U uFit a q depth,
    exact_CheckedSingletonInstanceCode U uFit a r depth,?_⟩
  have original := (exact_CheckedRawWitnessExists S K G T p pFit q r).mp ⟨cert,accepted⟩
  rcases exact_SubstitutionWindowStep S K _ _ T q r (.cons a .nil) depth closed compatible original with yes | ⟨eq,σ,bottom⟩
  · exact Or.inl ((exact_CheckedRawWitnessExists S K H T p pFit x y).mpr yes)
  · have member : NTerm.bottom σ ∈ [a] := bottom
    exact Or.inr ⟨congrArg encodeTerm eq,⟨σ,(List.mem_singleton.mp member).symm⟩⟩

/-- A typed variable opening cannot collapse. The substituted term
uses the exactly compiled instance at discharged depth zero. -/
theorem exact_CheckedFreshOpening (S : Spine.Signature) (K G : List Ty) (σ T : Ty)
    (U : Program 3) (p : Program 5) (uFit : DepthInstanceFit U)
    (pFit : ActualRawCalibration S.entries (fixed S K) p)
    (closed : DecisionSourceUniverse.Closed K) (σin : σ ∈ K) (q r : NTerm) (name cert : Nat)
    (accepted : evaluate p (canonicalTape (σ :: G) T (encodeTerm q) cert (encodeTerm r)) = 1) :
    ∃ q' r', evaluate U (encodeTerm (NTerm.free σ name) ::ᵥ 0 ::ᵥ encodeTerm q ::ᵥ nil) = q' + 1 ∧
      evaluate U (encodeTerm (NTerm.free σ name) ::ᵥ 0 ::ᵥ encodeTerm r ::ᵥ nil) = r' + 1 ∧
      ∃ after, evaluate p (canonicalTape G T q' after r') = 1 := by
  let a := NTerm.free σ name
  let x := substitute (.cons a .nil) 0 q
  let y := substitute (.cons a .nil) 0 r
  have original := (exact_CheckedRawWitnessExists S K (σ :: G) T p pFit q r).mp ⟨cert,accepted⟩
  have target := exact_FreeSubstitutionWindowStep S K (Spine.BoundContext.«prefix» G Spine.EmptyContext)
    σ T q r name closed σin original
  exact ⟨encodeTerm x,encodeTerm y,exact_CheckedSingletonInstanceCode U uFit a q 0,
    exact_CheckedSingletonInstanceCode U uFit a r 0,(exact_CheckedRawWitnessExists S K G T p pFit x y).mpr target⟩

#print axioms exact_CheckedSingletonInstanceCode
#print axioms exact_CheckedSingletonRawPreservation
#print axioms exact_CheckedFreshOpening
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonRawPreservationProof
