module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceChildProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfEqual)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (childAt measureAt)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (reportTest intrinsicQuery)
open NumberedWindowInternalAuxWindowOpenTargets (contextTable windowGraph)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext earlierValue)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem actualReportedAuxChild (R C : Program 4) (slot : Nat) (ctx prior old raw ty : OTerm α)
    (small : Nonempty (Derivation body Γ (ltF raw (suc prior))))
    (field : Nonempty (Derivation body Γ (programGraph (childAt slot) raw ![prior,old,ctx,z])))
    (code : Nonempty (Derivation body Γ (programGraph C (suc ty) ![prior,old,ctx,z])))
    (table : Nonempty (Derivation body Γ (contextTable R old prior ctx)))
    (child : Nonempty (Derivation body Γ (windowGraph (intrinsicQuery (selectedIntrinsic R)) ctx ty raw))) :
    Nonempty (Derivation body Γ (programGraph (reportTest slot C) (suc z) ![prior,old,ctx,z])) := by
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have selected := (exact_OpenIntrinsicQuery (selectedIntrinsic R) body α Γ ctx ty raw).mp child
  have row := (sameContext R (suc ty) ctx raw).mp selected
  have earlier := earlierValue R slot raw (suc ty) prior old ctx field small row table
  have exactEq := equalityOfEqual (body := body) (Gamma := Γ) (suc ty) (suc ty) ⟨refl (suc ty)⟩
  exact binaryGraph equalityTest (measureAt slot) C (suc z) (suc ty) (suc ty) xs exactEq earlier code

#print axioms actualReportedAuxChild

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceChildProof
