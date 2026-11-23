module
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowOriginalLeastFeatureProof
import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankCalibrationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowOriginalApplicationRawRankProof
open NumberedWindowAddressApplication (graph application applyAddresses arrowView)
open NumberedWindowScalarAlgorithm (Settings scalar least edge vertices canonical)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowFieldAlgorithm (pack)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicPositiveAddressSyntaxProof (literalView)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank)
open NumberedWindowNeutralSpineRankCalibrationProof (exact_RawNeutralShapeFromRank exact_RawNeutralRankFromShape)
open NumberedWindowNeutralSpineRawRankProof (NeutralSpineRank)
open NumberedWindowOriginalLeastFeatureProof (exact_OriginalLeastPreservesFeature)

private theorem scalarPacked {s : Settings} {c t k : Nat}
    (accept : scalar s (packedAddress c t k) = true) :
    ∃ ctx, addressView (packedAddress c t k) = some (ctx,t,k) := by
  unfold scalar at accept
  rw [literalView] at accept ⊢
  cases h : contextView c with
  | none => simp [h] at accept
  | some ctx =>
    cases ht : typeBit t with
    | false => simp [h,ht] at accept
    | true => exact ⟨ctx,by simp [h,ht]⟩

private theorem applicationReport {s : Settings} {f u y fn ty : Nat} {ctx : List Nat}
    (source : addressView f = some (ctx,ty,fn)) (accepted : graph s f u y = true) :
    ∃ dom cod arg k, least s ctx cod (auxRaw dom cod fn arg) = some k ∧
      y = packedAddress (pack ctx) cod k := by
  have run : application s f u = some y := beq_iff_eq.mp accepted
  unfold application at run
  rw [source] at run
  cases view : addressView u with
  | none => simp [view] at run
  | some a =>
    obtain ⟨aCtx,aTy,arg⟩ := a
    have actual : applyAddresses s (ctx,ty,fn) (aCtx,aTy,arg) = some y := by
      rw [view] at run
      exact run
    unfold applyAddresses at actual
    cases arrow : arrowView ty with
    | none => simp [arrow] at actual
    | some ar =>
      obtain ⟨dom,cod⟩ := ar
      rw [arrow] at actual
      change (if (canonical s (ctx,ty,fn) && canonical s (aCtx,aTy,arg) &&
          (ctx == aCtx) && (dom == aTy)) = true then
        (least s ctx cod (auxRaw dom cod fn arg)).map
          (fun k => packedAddress (pack ctx) cod k) else none) = some y at actual
      split at actual
      next _ =>
        cases found : least s ctx cod (auxRaw dom cod fn arg) with
        | none =>
          change (least s ctx cod (auxRaw dom cod fn arg)).map
            (fun k => packedAddress (pack ctx) cod k) = some y at actual
          simp [found] at actual
        | some k =>
          change (least s ctx cod (auxRaw dom cod fn arg)).map
            (fun k => packedAddress (pack ctx) cod k) = some y at actual
          have out : packedAddress (pack ctx) cod k = y := by simpa [found] using actual
          exact ⟨dom,cod,arg,k,found,out.symm⟩
      next _ => cases actual

theorem exact_OriginalApplicationFunctionAddress (s : Settings) (f u y : Nat)
    (accepted : graph s f u y = true) :
    ∃ ctx ty fn, addressView f = some (ctx,ty,fn) := by
  have run : application s f u = some y := beq_iff_eq.mp accepted
  unfold application at run
  cases h : addressView f with
  | none => simp [h] at run
  | some q =>
    obtain ⟨ctx,ty,fn⟩ := q
    exact ⟨ctx,ty,fn,rfl⟩

/-- Accepted original application preserves positive neutral rank, and
the exact raw rank increases by one. The original exchange preservation
hypothesis is explicit and local to the actual edge invoked by least. -/
theorem exact_OriginalApplicationRawRank (s : Settings) (f u y fn ty : Nat) (ctx : List Nat)
    (transport : ∀ g t a b, edge s g t a b = true → rawRank b = rawRank a)
    (source : addressView f = some (ctx,ty,fn)) (accepted : graph s f u y = true)
    (carrier : scalar s y = true) (positive : rawRank fn ≠ 0) :
    ∃ yCtx yTy k, addressView y = some (yCtx,yTy,k) ∧ rawRank k = rawRank fn + 1 := by
  obtain ⟨dom,cod,arg,k,found,emit⟩ := applicationReport source accepted
  have rankSeed : rawRank (auxRaw dom cod fn arg) = rawRank fn + 1 := by
    cases h : rawRank fn with
    | zero => exact False.elim (positive h)
    | succ n =>
      have shp : NeutralSpineRank fn n := exact_RawNeutralShapeFromRank fn n h
      exact exact_RawNeutralRankFromShape (NeutralSpineRank.aux dom cod arg shp)
  have moves := exact_OriginalLeastPreservesFeature (edge s ctx cod)
    (vertices s (auxRaw dom cod fn arg)) (auxRaw dom cod fn arg) k rawRank (transport ctx cod) found
  have out := scalarPacked (s := s) (c := pack ctx) (t := cod) (k := k) (emit ▸ carrier)
  obtain ⟨γ,view⟩ := out
  exact ⟨γ,cod,k,by simpa only [emit] using view,moves.trans rankSeed⟩

#print axioms exact_OriginalApplicationRawRank
#print axioms exact_OriginalApplicationFunctionAddress
end LogicLineages.PersistentMarking.NumberedWindowOriginalApplicationRawRankProof
