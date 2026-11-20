module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationRoundsProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveAddressSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterAddressProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationAddressProof
open NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowAtomicApplicationRoundsProof (atomicLeast)
open NumberedWindowAtomicPositiveAddressSyntaxProof (literalView contextCode)
open NumberedWindowInternalFreshProbeParsedEmitterAddressProof (addressCoordinates)
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowAddressAlgorithm (addressView contextView typeBit)
open NumberedWindowAddressApplication (graph application applyAddresses arrowView)
open NumberedWindowScalarAlgorithm (Settings canonical least)

theorem actualApplication : ExactAtomicAuxOriginalApplication := by
  intro s rawCtx functionType fn argument value atom h
  have accepted : application s (packedAddress rawCtx functionType fn) argument = some value :=
    beq_iff_eq.mp h
  unfold application at accepted
  rw [literalView] at accepted
  cases hCtx : contextView rawCtx with
  | none => simp [hCtx] at accepted
  | some Γ =>
    cases hTy : typeBit functionType with
    | false => simp [hCtx,hTy] at accepted
    | true =>
      cases hArg : addressView argument with
      | none => simp [hCtx,hTy,hArg] at accepted
      | some target =>
        rcases target with ⟨argCtx,argTy,argRaw⟩
        have run : applyAddresses s (Γ,functionType,fn) (argCtx,argTy,argRaw) = some value := by
          simpa [hCtx,hTy,hArg] using accepted
        unfold applyAddresses at run
        cases hArr : arrowView functionType with
        | none => simp [hArr] at run
        | some ar =>
          rcases ar with ⟨dom,cod⟩
          let guard := canonical s (Γ,functionType,fn) && canonical s (argCtx,argTy,argRaw) &&
            (Γ == argCtx) && (dom == argTy)
          let rawApp := auxRaw dom cod fn argRaw
          have pieces : guard = true ∧
              (least s Γ cod rawApp).map (fun n => packedAddress (pack Γ) cod n) = some value := by
            simpa [hArr,guard,rawApp,auxRaw,packedAddress] using run
          obtain ⟨bits,actual⟩ := pieces
          simp only [guard,Bool.and_eq_true,beq_iff_eq,and_assoc] at bits
          obtain ⟨_,_,sameCtx,sameType⟩ := bits
          subst argCtx
          subst argTy
          cases hLeast : least s Γ cod rawApp with
          | none => simp [hLeast] at actual
          | some representative =>
            have sameValue : packedAddress (pack Γ) cod representative = value := by
              simpa [hLeast] using actual
            obtain ⟨argOut,rep,trace⟩ :=
              (atomicLeast s Γ cod dom cod fn argRaw representative atom).1 hLeast
            have sameContext := contextCode hCtx
            have sameArgument := (addressCoordinates hArg).1
            refine ⟨dom,cod,argRaw,argOut,?_,?_,?_,trace⟩
            · first | exact hArr | rfl
            · rw [sameContext]
              exact sameArgument
            · rw [sameContext,← sameValue,rep]

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationAddressProof
