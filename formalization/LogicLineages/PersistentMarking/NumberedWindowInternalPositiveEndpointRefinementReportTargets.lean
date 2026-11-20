module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (someAddressPositive)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)

/-- The same actual shared address/fiber report plus the two actual
scalar Program graphs, not reports of independent parsed witnesses. -/
def guardedReport {α : Type} (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
    (left witness right : OTerm α) : Formula α :=
  let one : OTerm α := OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm
  someAddressPositive cv tv raw least left witness right ⊓
    (programGraph i one ![left] ⊓ programGraph i one ![right])

/-- Both real object implications, under any fixed body and open
hypotheses, for the very same physical accepted tape and witness. -/
def ExactOpenEndpointRefinedReport : Prop :=
  ∀ (i cv tv : Program 1) (raw : Program 5) (least : Program 3)
      (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (left witness right : OTerm α),
    let r := withEndpointCarriers i (addressPositive cv tv raw least)
    let accepted := accepts r left witness right
    let reported := guardedReport i cv tv raw least left witness right
    Nonempty (Derivation B Γ ((accepted.imp reported) ⊓ (reported.imp accepted)))

/-- The new actual installed report, at every outer context, with the
literal guards included. No old-body report is reused by transport. -/
def ExactInstalledEndpointRefinedReport : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3)
      (c : Nat) (α : Type) (left witness right : OTerm α),
    let r := withEndpointCarriers i (addressPositive cv tv raw least)
    let B := sourceBody (data i j r d) c
    let accepted := accepts r left witness right
    let reported := guardedReport i cv tv raw least left witness right
    Nonempty (Derivation B [] ((accepted.imp reported) ⊓ (reported.imp accepted)))

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementReportTargets
