module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressSingletonChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftSingletonProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm functionWitnessTerm)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonInputs)
open NumberedWindowInternalSparseAddressSingletonChecks (exact_OpenInstalledSingleton)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets
open NumberedWindowInternalSparseTypedRawLiftGraphProof (wrap)

theorem singleton : ExactOpenInstalledTypedRaw5LiftedSingleton := by
  intro i j cv tv d root other windowProg least syntaxProg c α Γ
    left right ctx dom cod sourceClass destClass arg source child dest
  let raw := typedRaw5 root other windowProg syntaxProg
  let R := addressPositive cv tv raw least
  let B := sourceBody (data i j R d) c
  let src := auxiliaryTerm dom cod source arg
  let wr := functionWitnessTerm child
  let dst := auxiliaryTerm dom cod dest arg
  let assumptions := liftInputs root other windowProg syntaxProg ctx dom cod arg source child dest ⊓
    liftedSingletonFacts cv tv least left right ctx cod sourceClass destClass src dst
  let Δ := assumptions :: Γ
  have premise : Derivation B Δ assumptions := Derivation.hypothesis List.mem_cons_self
  obtain ⟨lifted⟩ := wrap (body := B) (Γ := Δ) root other windowProg syntaxProg
    ctx dom cod arg source child dest ⟨Derivation.conjunctionLeft premise⟩
  have reports := Derivation.conjunctionRight premise
  have afterLeft := Derivation.conjunctionRight reports
  have afterRight := Derivation.conjunctionRight afterLeft
  have afterContext := Derivation.conjunctionRight afterRight
  have inputs : Derivation B Δ
      (singletonInputs cv tv raw least left right ctx cod sourceClass destClass src wr dst) :=
    Derivation.conjunctionIntroduction (Derivation.conjunctionLeft reports)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft afterLeft)
        (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft afterRight)
          (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft afterContext)
            (Derivation.conjunctionIntroduction lifted (Derivation.conjunctionRight afterContext)))))
  obtain ⟨oneHop⟩ := closedApply
    (exact_OpenInstalledSingleton i j cv tv d raw least c α
      left right ctx cod sourceClass destClass src wr dst) ⟨inputs⟩
  exact ⟨Derivation.implicationIntroduction oneHop⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftSingletonProof
