module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericSideProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericCompositionProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowPositivePathAlgorithm (addressRS)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalSparsePositiveFoldTargets (ActualPositiveCalibration)
open NumberedWindowInternalSparseAddressPositive
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof
open NumberedWindowInternalSparseAddressPositiveNumericSlotsProof
open NumberedWindowInternalSparseAddressPositiveNumericSideProof

private abbrev step (entries : Entries) (s : Settings) := NumberedWindowConcreteCheckers.step entries s
private abbrev leastOf (s : Settings) := NumberedWindowScalarAlgorithm.least s

private theorem fromOriginal {entries : Entries} {s : Settings} {cv tv : Program 1} {raw : Program 5} {least : Program 3}
    (hc : ActualContextGuard cv) (ht : ActualTypeGuard tv) (cal : ActualPositiveCalibration entries s raw least)
    (x w y : Nat) (h : addressRS (step entries s) (leastOf s) x w y = true) :
    sideReports cv tv x ∧ (sideReports cv tv y ∧
      (NumberedWindowInternalSparsePathEnvelope.run rawContext x =
        NumberedWindowInternalSparsePathEnvelope.run rawContext y ∧
      (NumberedWindowInternalSparsePathEnvelope.run rawResult x =
        NumberedWindowInternalSparsePathEnvelope.run rawResult y ∧
       evaluate (callFold raw least) (tape x w y) = 1))) := by
  cases hx : addressView x with
  | none => simp [addressRS,hx] at h
  | some lx =>
    rcases lx with ⟨Γ,t,b⟩
    cases hy : addressView y with
    | none => simp [addressRS,hx,hy] at h
    | some ry =>
      rcases ry with ⟨Δ,u,c⟩
      have tests : ((Γ == Δ) = true ∧ (t == u) = true) ∧
          NumberedWindowPositivePathAlgorithm.positive (step entries s) (leastOf s) Γ t b w c = true := by
        simpa only [addressRS,hx,hy,Bool.and_eq_true,and_assoc] using h
      have stackEq : Γ = Δ := by simpa using tests.1.1
      have typeEq : t = u := by simpa using tests.1.2
      obtain ⟨l,ls,lt,lk⟩ := viewDecoded hx
      obtain ⟨r,rs,rt,rk⟩ := viewDecoded hy
      have ce := (sameContext l.contextOk r.contextOk).mpr (ls.trans (stackEq.trans rs.symm))
      have te := lt.trans (typeEq.trans rt.symm)
      have pos := (coreOf cal w l r).mpr (by simpa only [ls,lt,lk,rk] using tests.2)
      exact ⟨reportsOf hc ht l,reportsOf hc ht r,
        (fields l).1.trans (ce.trans (fields r).1.symm),
        (fields l).2.1.trans (te.trans (fields r).2.1.symm),pos⟩

private theorem fromSelected {entries : Entries} {s : Settings} {cv tv : Program 1} {raw : Program 5} {least : Program 3}
    (hc : ActualContextGuard cv) (ht : ActualTypeGuard tv) (cal : ActualPositiveCalibration entries s raw least)
    (x w y : Nat)
    (h : sideReports cv tv x ∧ (sideReports cv tv y ∧
      (NumberedWindowInternalSparsePathEnvelope.run rawContext x =
        NumberedWindowInternalSparsePathEnvelope.run rawContext y ∧
      (NumberedWindowInternalSparsePathEnvelope.run rawResult x =
        NumberedWindowInternalSparsePathEnvelope.run rawResult y ∧
       evaluate (callFold raw least) (tape x w y) = 1)))) :
    addressRS (step entries s) (leastOf s) x w y = true := by
  obtain ⟨lx,ry,ctx,type,fold⟩ := h
  obtain ⟨l⟩ := decodedOf hc ht lx
  obtain ⟨r⟩ := decodedOf hc ht ry
  have ce := (fields l).1.symm.trans (ctx.trans (fields r).1)
  have se := (sameContext l.contextOk r.contextOk).mp ce
  have te := (fields l).2.1.symm.trans (type.trans (fields r).2.1)
  have cb : (l.stack == r.stack) = true := by simp [se]
  have tb : (l.ty == r.ty) = true := by simp [te]
  have good := (coreOf cal w l r).mp fold
  simp only [addressRS,decodedView l,decodedView r,cb,tb,Bool.true_and]
  exact good

private theorem atOne {entries : Entries} {s : Settings} {cv tv : Program 1} {raw : Program 5} {least : Program 3}
    (hc : ActualContextGuard cv) (ht : ActualTypeGuard tv) (cal : ActualPositiveCalibration entries s raw least)
    (x w y : Nat) :
    evaluate (addressPositive cv tv raw least) (tape x w y) = 1 ↔
      addressRS (step entries s) (leastOf s) x w y = true := by
  simp only [addressPositive,acceptedBoth,sourceSide,targetSide,sameTest]
  exact ⟨fromSelected hc ht cal x w y,fromOriginal hc ht cal x w y⟩

private theorem bit (cv tv : Program 1) (raw : Program 5) (least : Program 3) (x w y : Nat) :
    evaluate (addressPositive cv tv raw least) (tape x w y) = 0 ∨
    evaluate (addressPositive cv tv raw least) (tape x w y) = 1 := by
  unfold addressPositive
  rw [conjunctionEvaluation]
  split <;> simp

theorem composition : AddressPositiveComposition := by
  intro entries s cv tv raw least hc ht cal x w y
  change evaluate (addressPositive cv tv raw least) (tape x w y) =
    (addressRS (step entries s) (leastOf s) x w y).toNat
  by_cases h : addressRS (step entries s) (leastOf s) x w y = true
  · rw [(atOne hc ht cal x w y).mpr h,h] <;> rfl
  · have no : addressRS (step entries s) (leastOf s) x w y = false := by
      cases e : addressRS (step entries s) (leastOf s) x w y <;> simp_all
    rw [no]
    rcases bit cv tv raw least x w y with b | b
    · exact b
    · exact False.elim (h ((atOne hc ht cal x w y).mp b))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericCompositionProof
