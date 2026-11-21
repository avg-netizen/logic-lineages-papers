module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreNumericChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSourceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView Address)
open NumberedWindowAddressApplication (arrowView applyAddresses application graph)
open NumberedWindowScalarAlgorithm (Settings canonical)
open NumberedWindowFieldAlgorithm (pack unpack packNode)
open NumberedWindowInternalFreshProbeParsedEmitter
  (addressGood arrowGood rawContext rawResult rawLeast rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates arrowMissing exactCoordinates)
open NumberedWindowInternalSparseAddressPositiveNumericShapeProof (viewDecoded unpackContext)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (packOfUnpack)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration packedLeast)
open NumberedWindowInternalSparseApplicationOutputCore (outputCore)
open NumberedWindowInternalSparseApplicationOutputCoreTargets (originalOutput)
open NumberedWindowInternalSparseApplicationOutputCoreNumericChecks (exact_AllInputApplicationOutputCore)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationFrontendNumericSlotsProof (tape coreAtOne)

private theorem unpackPackedView {q ty k : Nat} {g : List Nat} (h : addressView q = some (g,ty,k)) :
    unpack (pack g) = some g := by
  obtain ⟨d,stack,_,_⟩ := viewDecoded h
  have w := unpackContext d.contextOk
  rw [packOfUnpack d.ctx w,stack] at w
  exact w

private theorem packedEq {f u ft ut fk uk : Nat} {g d : List Nat}
    (fv : addressView f = some (g,ft,fk)) (uv : addressView u = some (d,ut,uk)) :
    pack g = pack d ↔ g = d := by
  constructor
  · intro same
    have h := (unpackPackedView fv).symm.trans
      ((congrArg unpack same).trans (unpackPackedView uv))
    exact Option.some.inj h
  · exact congrArg pack

private theorem outputWithView (s : Settings) {f ft fk : Nat} {g : List Nat}
    (fv : addressView f = some (g,ft,fk)) (dom cod arg : Nat) :
    originalOutput s (pack g) dom cod fk arg =
      (NumberedWindowScalarAlgorithm.least s g cod (packNode 6 [dom,cod,fk,arg])).map
        (fun k => packNode 3 [pack g,cod,k]) := by
  simp only [originalOutput,packedLeast,unpackPackedView fv,Option.bind_some]

theorem coreAtViews {s : Settings} {least : Program 3} (cal : ActualLeastCalibration s least)
    (f u y ft ut fk uk : Nat) (g d : List Nat)
    (fv : addressView f = some (g,ft,fk)) (uv : addressView u = some (d,ut,uk))
    (fc : canonical s (g,ft,fk) = true) (uc : canonical s (d,ut,uk) = true) :
    evaluate (applicationCore least) (tape f u y) = 1 ↔ graph s f u y = true := by
  rw [coreAtOne]
  obtain ⟨_,shapeU,ctxU,resultU,leastU⟩ := addressCoordinates uv
  cases ar : arrowView ft with
  | none =>
    obtain ⟨_,_,_,actualType,_⟩ := addressCoordinates fv
    have reject := arrowMissing actualType ar
    simp [reject,graph,application,fv,uv,applyAddresses,ar]
  | some de =>
    rcases de with ⟨dom,cod⟩
    obtain ⟨_,shapeF,arrowF,ctxF,_,leastF,domainF,codomainF⟩ := exactCoordinates f g ft fk dom cod fv ar
    have output := exact_AllInputApplicationOutputCore s least cal (pack g) dom cod fk uk y
    let selected := (NumberedWindowScalarAlgorithm.least s g cod (packNode 6 [dom,cod,fk,uk])).map
      (fun k => packNode 3 [pack g,cod,k])
    have sourceViews : application s f u = applyAddresses s (g,ft,fk) (d,ut,uk) := by
      unfold application
      rw [fv]
      change ((addressView u).bind fun a => applyAddresses s (g,ft,fk) a) = _
      rw [uv] <;> rfl
    have sourceArrow : applyAddresses s (g,ft,fk) (d,ut,uk) =
        if (g == d) && (dom == ut) then selected else none := by
      unfold applyAddresses
      change (arrowView ft).bind (fun a => match a with
        | (m,n) => if canonical s (g,ft,fk) && canonical s (d,ut,uk) && (g == d) && (m == ut) then
            (NumberedWindowScalarAlgorithm.least s g n (packNode 6 [m,n,fk,uk])).map
              (fun k => packNode 3 [pack g,n,k])
          else none) = _
      rw [ar]
      change (if canonical s (g,ft,fk) && canonical s (d,ut,uk) && (g == d) && (dom == ut)
        then selected else none) = _
      simp only [fc,uc,Bool.true_and]
    have outValue : originalOutput s (pack g) dom cod fk uk = selected :=
      outputWithView s fv dom cod uk
    have oneBit (b : Bool) : b.toNat = 1 ↔ b = true := by cases b <;> simp
    simp only [shapeF,shapeU,arrowF,ctxF,ctxU,domainF,resultU,codomainF,leastF,leastU,
      output,outValue,oneBit,graph,sourceViews,sourceArrow]
    have packed := packedEq fv uv
    by_cases sc : g = d
    · have scb : (g == d) = true := by simp [sc]
      by_cases td : dom = ut
      · have tdb : (dom == ut) = true := by simp [td]
        have pass : (true && true) = true := rfl
        rw [scb,tdb,if_pos pass]
        change (True ∧ (True ∧ (True ∧ (pack g = pack d ∧
          (dom = ut ∧ (selected == some y) = true))))) ↔ (selected == some y) = true
        exact ⟨fun ⟨_,_,_,_,_,h⟩ => h, fun h => ⟨True.intro,True.intro,True.intro,packed.mpr sc,td,h⟩⟩
      · have tdb : (dom == ut) = false :=
          Bool.eq_false_iff.mpr (fun h => td (eq_of_beq h))
        have reject : (true && false) ≠ true := by
          intro impossible
          change false = true at impossible
          cases impossible
        rw [scb,tdb,if_neg reject]
        change (True ∧ (True ∧ (True ∧ (pack g = pack d ∧
          (dom = ut ∧ (selected == some y) = true))))) ↔ (false : Bool) = true
        exact ⟨fun ⟨_,_,_,_,h,_⟩ => False.elim (td h),fun h => nomatch h⟩
    · have scb : (g == d) = false := Bool.eq_false_iff.mpr (fun h => sc (eq_of_beq h))
      have reject : (false && (dom == ut)) ≠ true := by
        intro impossible
        change false = true at impossible
        cases impossible
      rw [scb,if_neg reject]
      change (True ∧ (True ∧ (True ∧ (pack g = pack d ∧
        (dom = ut ∧ (selected == some y) = true))))) ↔ (false : Bool) = true
      exact ⟨fun ⟨_,_,_,h,_,_⟩ => False.elim (sc (packed.mp h)),fun h => nomatch h⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSourceProof
