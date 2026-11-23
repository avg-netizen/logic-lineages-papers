module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSettingsGrammarGuardNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowAddressAlgorithm (typeBit addressView)
open NumberedWindowScalarAlgorithm (Settings scalar canonical)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard grammarTypeAt)
open NumberedWindowInternalSettingsGrammarGuardNumericTargets (GrammarTypeInclusion)
open NumberedWindowInternalSettingsGrammarGuardNumericProof (exact_SettingsRefitGuardCalibration)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (run applyUnary)
open NumberedWindowInternalSparsePathEnvelopeArityEvaluationProof (applyValue)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualContextGuard ActualTypeGuard)
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof (Decoded decodedView viewDecoded)
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof (acceptedBoth sideReports)
open NumberedWindowInternalSparseAddressPositiveNumericSideProof (fields decodedOf)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalSparseCanonicalAddressTargets
open NumberedWindowInternalCoverMeasuredApplicationTypeCalibrationTargets (refittedScalarType)
open NumberedWindowInternalCoverMeasuredApplicationRefittedInstallTargets

private theorem boolOne (b : Bool) : b.toNat = 1 ↔ b = true := by
  cases b <;> decide

private theorem bitValue {x : Nat} {b : Bool} (bit : x = 0 ∨ x = 1) (iff : x = 1 ↔ b = true) :
    x = b.toNat := by
  cases b with
  | false =>
    rcases bit with h | h
    · exact h
    · exact absurd (iff.mp h) (by decide)
  | true => exact iff.mpr rfl

private theorem conjBit {n : Nat} (p q : Program n) (v : List.Vector Nat n) :
    evaluate (conjunction p q) v = 0 ∨ evaluate (conjunction p q) v = 1 := by
  rw [conjunctionEvaluation]
  split <;> simp

private theorem guardSplit (s : Settings) (n : Nat) :
    typeGuard s n = true ↔ typeBit n = true ∧ s.window.1.contains n = true := by
  show (typeBit n && s.window.1.contains n) = true ↔ _
  exact Bool.and_eq_true_iff

private theorem refittedValue {s : Settings} {TV T : Program 1} (inc : GrammarTypeInclusion s)
    (hTV : ActualTypeGuard TV) (hT : TypeGuardCalibrated s T) (n : Nat) :
    evaluate (refittedScalarType s TV T) (n ::ᵥ nil) = (typeGuard s n).toNat := by
  have refit : evaluate (refitGuard s T) (n ::ᵥ nil) = (typeGuard s n).toNat :=
    exact_SettingsRefitGuardCalibration s T inc hT n
  have iff : evaluate (conjunction TV (refitGuard s T)) (n ::ᵥ nil) = 1 ↔
      typeGuard s n = true := by
    constructor
    · intro one
      have r := ((acceptedBoth TV (refitGuard s T) (n ::ᵥ nil)).mp one).2
      rw [refit] at r
      exact (boolOne _).mp r
    · intro g
      have tb : typeBit n = true := ((guardSplit s n).mp g).1
      refine (acceptedBoth TV (refitGuard s T) (n ::ᵥ nil)).mpr ⟨?_, ?_⟩
      · rw [hTV n]
        exact (boolOne _).mpr tb
      · rw [refit]
        exact (boolOne _).mpr g
  exact bitValue (conjBit TV (refitGuard s T) (n ::ᵥ nil)) iff

private theorem guardEqBit {s : Settings} (all : AllTypesWindowed s) (n : Nat) :
    typeGuard s n = typeBit n := by
  by_cases tb : typeBit n = true
  · rw [tb]
    exact (guardSplit s n).mpr ⟨tb, all n tb⟩
  · by_cases g : typeGuard s n = true
    · exact absurd ((guardSplit s n).mp g).1 tb
    · exact (eq_false_of_ne_true g).trans (eq_false_of_ne_true tb).symm

theorem exact_RefittedScalarTypeCalibrated : ExactRefittedScalarTypeCalibrated := by
  intro s TV T inc hTV hT n
  exact refittedValue inc hTV hT n

theorem exact_RefittedTypeGuardActualOnlyIf : ExactRefittedTypeGuardActualOnlyIf := by
  intro s TV T hT actual n tb
  have one : evaluate (conjunction TV (refitGuard s T)) (n ::ᵥ nil) = 1 :=
    (actual n).trans (congrArg Bool.toNat tb)
  have r : evaluate (conjunction T (grammarTypeAt s)) (n ::ᵥ nil) = 1 :=
    ((acceptedBoth TV (refitGuard s T) (n ::ᵥ nil)).mp one).2
  have t : evaluate T (n ::ᵥ nil) = 1 :=
    ((acceptedBoth T (grammarTypeAt s) (n ::ᵥ nil)).mp r).1
  have c : evaluate T (n ::ᵥ nil) = (typeGuard s n).toNat := hT n
  rw [c] at t
  exact ((guardSplit s n).mp ((boolOne _).mp t)).2

theorem exact_RefittedTypeGuardActualIff : ExactRefittedTypeGuardActualIff := by
  intro s TV T inc hTV hT
  constructor
  · exact exact_RefittedTypeGuardActualOnlyIf s TV T hT
  · intro all n
    exact (refittedValue inc hTV hT n).trans (congrArg Bool.toNat (guardEqBit all n))

theorem exact_RefittedInstalledTupleOnlyIf : ExactRefittedInstalledTupleOnlyIf := by
  intro xs s W i j cv TV T d p₀ raw least v hT installed
  obtain ⟨_, _, callbacks, _⟩ := installed
  obtain ⟨_, actual, _⟩ := callbacks
  exact exact_RefittedTypeGuardActualOnlyIf s TV T hT actual

private theorem shapeOne (cv tv : Program 1) (q : Nat) :
    run (shapeChecks cv tv) q = 1 ↔ sideReports cv tv q := by
  change evaluate (shapeChecks cv tv) (q ::ᵥ nil) = 1 ↔ _
  simp only [shapeChecks,acceptedBoth,sideReports]
  change _ ∧ (run (applyUnary cv rawContext) q = 1 ∧ run (applyUnary tv rawResult) q = 1) ↔ _
  rw [applyValue,applyValue]
  rfl

private theorem scalarOne (cv tv : Program 1) (W least : Program 3) (q : Nat) :
    evaluate (addressScalar cv tv W least) (q ::ᵥ nil) = 1 ↔
      sideReports cv tv q ∧ run (coordinateCall W least) q = 1 := by
  constructor
  · intro h
    have both := (acceptedBoth (shapeChecks cv tv) (coordinateCall W least) (q ::ᵥ nil)).mp h
    exact ⟨(shapeOne cv tv q).mp both.1, both.2⟩
  · intro h
    exact (acceptedBoth (shapeChecks cv tv) (coordinateCall W least) (q ::ᵥ nil)).mpr
      ⟨(shapeOne cv tv q).mpr h.1, h.2⟩

private theorem scalarAt {s : Settings} {q : Nat} {ctx : List Nat} {ty k : Nat}
    (view : addressView q = some (ctx, ty, k)) :
    scalar s q = canonical s (ctx, ty, k) := by
  show (addressView q).any (canonical s) = canonical s (ctx, ty, k)
  exact congrArg (Option.any (canonical s)) view

private theorem scalarIff {s : Settings} {cv TV T : Program 1} {W least : Program 3}
    (inc : GrammarTypeInclusion s) (hc : ActualContextGuard cv) (hTV : ActualTypeGuard TV)
    (hT : TypeGuardCalibrated s T) (hw : ActualPackedWindow s W)
    (hl : ActualLeastCalibration s least) :
    ActualScalarCalibration s (addressScalar cv (refittedScalarType s TV T) W least) ↔
      AcceptedTypesWindowed s := by
  have orig : ∀ q, evaluate (addressScalar cv TV W least) (q ::ᵥ nil) = (scalar s q).toNat :=
    NumberedWindowInternalSparseCanonicalAddressNumericProof.calibration s cv TV W least
      hc hTV hw hl
  have refit : ∀ m, run (refittedScalarType s TV T) m = 1 ↔ typeGuard s m = true := by
    intro m
    have v : run (refittedScalarType s TV T) m = (typeGuard s m).toNat :=
      refittedValue inc hTV hT m
    rw [v]
    exact boolOne _
  have plain : ∀ m, run TV m = 1 ↔ typeBit m = true := by
    intro m
    have v : run TV m = (typeBit m).toNat := hTV m
    rw [v]
    exact boolOne _
  constructor
  · intro cal q ctx ty k view can
    obtain ⟨d, _, dty, _⟩ := viewDecoded view
    have accepted : scalar s q = true := (scalarAt view).trans can
    have one : evaluate (addressScalar cv (refittedScalarType s TV T) W least) (q ::ᵥ nil) = 1 :=
      (cal q).trans (congrArg Bool.toNat accepted)
    obtain ⟨side, _⟩ := (scalarOne cv (refittedScalarType s TV T) W least q).mp one
    obtain ⟨_, _, ty1⟩ := side
    rw [(fields d).2.1, dty] at ty1
    exact ((guardSplit s ty).mp ((refit ty).mp ty1)).2
  · intro windowed q
    have bit : evaluate (addressScalar cv (refittedScalarType s TV T) W least) (q ::ᵥ nil) = 0 ∨
        evaluate (addressScalar cv (refittedScalarType s TV T) W least) (q ::ᵥ nil) = 1 :=
      conjBit (shapeChecks cv (refittedScalarType s TV T)) (coordinateCall W least) (q ::ᵥ nil)
    refine bitValue bit ?_
    constructor
    · intro one
      obtain ⟨side, co⟩ := (scalarOne cv (refittedScalarType s TV T) W least q).mp one
      obtain ⟨good, ctxOk, tyOk⟩ := side
      have tb : typeBit (run rawResult q) = true :=
        ((guardSplit s _).mp ((refit _).mp tyOk)).1
      have plainOne : evaluate (addressScalar cv TV W least) (q ::ᵥ nil) = 1 :=
        (scalarOne cv TV W least q).mpr ⟨⟨good, ctxOk, (plain _).mpr tb⟩, co⟩
      have v := orig q
      rw [plainOne] at v
      exact (boolOne _).mp v.symm
    · intro accepted
      have plainOne : evaluate (addressScalar cv TV W least) (q ::ᵥ nil) = 1 :=
        (orig q).trans (congrArg Bool.toNat accepted)
      obtain ⟨side, co⟩ := (scalarOne cv TV W least q).mp plainOne
      obtain ⟨d⟩ := decodedOf hc hTV side
      have view := decodedView d
      have can : canonical s (d.stack, d.ty, d.classCode) = true :=
        (scalarAt view).symm.trans accepted
      have listed : s.window.1.contains d.ty = true :=
        windowed q d.stack d.ty d.classCode view can
      have g : typeGuard s d.ty = true := (guardSplit s d.ty).mpr ⟨d.typeOk, listed⟩
      obtain ⟨good, ctxOk, _⟩ := side
      have tyOk : run (refittedScalarType s TV T) (run rawResult q) = 1 := by
        rw [(fields d).2.1]
        exact (refit d.ty).mpr g
      exact (scalarOne cv (refittedScalarType s TV T) W least q).mpr ⟨⟨good, ctxOk, tyOk⟩, co⟩

theorem exact_RefittedAddressScalarCalibrationIff :
    ExactRefittedAddressScalarCalibrationIff := by
  intro s cv TV T W least inc hc hTV hT hw hl
  exact scalarIff inc hc hTV hT hw hl

theorem exact_RefittedInstalledScalarCalibrationIff :
    ExactRefittedInstalledScalarCalibrationIff := by
  intro V TV M M0 B T base s cv root other Q inc hc hTV hT hw hl
  exact scalarIff inc hc hTV hT hw hl

#print axioms exact_RefittedScalarTypeCalibrated
#print axioms exact_RefittedTypeGuardActualOnlyIf
#print axioms exact_RefittedTypeGuardActualIff
#print axioms exact_RefittedInstalledTupleOnlyIf
#print axioms exact_RefittedAddressScalarCalibrationIff
#print axioms exact_RefittedInstalledScalarCalibrationIff
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationRefittedInstallProof
