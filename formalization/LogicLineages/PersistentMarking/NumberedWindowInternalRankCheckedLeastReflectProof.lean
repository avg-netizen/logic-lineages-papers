module

public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastObjectProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReflectProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (valueUnique outputTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Rename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalRankCheckedLeast (checkedLeast)
open NumberedWindowInternalRankCheckedLeastObjectProof (exact_OpenRankCheckedLeastConservation)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Backward transport of the actual observed rank along a successful
checked least report, using genuine graph existence and uniqueness.
This applies to zero or positive m without any decoder hypothesis. -/
theorem exact_OpenRankCheckedLeastReflect (g : Program 1) (L : Program 3)
    (ctx ty seed k m : OTerm α)
    (checked : Nonempty (Derivation B Γ (programGraph (checkedLeast g L) (suc k) ![ctx,ty,seed])))
    (known : Nonempty (Derivation B Γ (unary g m k))) :
    Nonempty (Derivation B Γ (unary g m seed)) := by
  apply programCases g (![seed] : Fin 1 → OTerm α) (unary g m seed)
  intro β j Δ n keep actual
  rw [unaryInputsRename] at actual
  rw [unaryRename]
  have h := renameInto checked j Δ keep
  rw [graph3Rename,sucRelabel] at h
  have heard := renameInto known j Δ keep
  rw [unaryRename] at heard
  have same := (exact_OpenRankCheckedLeastConservation g L (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (k.relabel j) n h actual).2
  have outputs := valueUnique g n (m.relabel j) ![k.relabel j] same heard
  exact outputTransport g n (m.relabel j) ![seed.relabel j] outputs actual

#print axioms exact_OpenRankCheckedLeastReflect
end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReflectProof
