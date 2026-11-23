module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAppliedEndpointReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique headTransport)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (auxAddressTerm)
open NumberedWindowInternalSparseAppliedEndpointReportProof (fromAddressEquation)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Physically align the selected least, its own retained address
coordinates, and the literal auxiliary output description on that
very same y. No seed-shape-to-least inference is involved. -/
structure ChosenAuxShape (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (ctx cod selected altCtx dom altCod head a' : OTerm α) : Prop where
  context : Nonempty (Derivation B Γ (eqn ctx altCtx))
  codomain : Nonempty (Derivation B Γ (eqn cod altCod))
  selectedEq : Nonempty (Derivation B Γ (eqn selected (auxiliaryTerm dom altCod head a')))
  selectedTag : Nonempty (Derivation B Γ (unary termShape (suc z) selected))
  selectedHead : Nonempty (Derivation B Γ (unary (field 2) head selected))

theorem exact_OpenAtomicAppliedLeastShape (y ctx cod selected altCtx dom altCod head a' : OTerm α)
    (selectedAddress : Nonempty (Derivation B Γ (eqn y (addressTerm ctx cod selected))))
    (observedAddress : Nonempty (Derivation B Γ (equal y (auxAddressTerm altCtx dom altCod head a')))) :
    ChosenAuxShape B Γ ctx cod selected altCtx dom altCod head a' := by
  let aux := auxiliaryTerm dom altCod head a'
  have observed : Nonempty (Derivation B Γ (eqn y (addressTerm altCtx altCod aux))) := by
    simpa only [equalEqn,auxAddressTerm,aux,auxiliaryTerm,
      NumberedWindowInternalFreshProbeEmitterObjectTargets.consTerm,
      NumberedWindowInternalSparsePathEnvelopeTargets.rawCons] using observedAddress
  obtain ⟨h₁⟩ := fromAddressEquation y ctx cod selected selectedAddress
  obtain ⟨h₂⟩ := fromAddressEquation y altCtx altCod aux observed
  let left := Derivation.conjunctionRight h₁
  let right := Derivation.conjunctionRight h₂
  let lc := Derivation.conjunctionRight left
  let rc := Derivation.conjunctionRight right
  have hc := valueUnique rawContext ctx altCtx ![y]
    ⟨Derivation.conjunctionLeft left⟩ ⟨Derivation.conjunctionLeft right⟩
  have ht := valueUnique rawResult cod altCod ![y]
    ⟨Derivation.conjunctionLeft lc⟩ ⟨Derivation.conjunctionLeft rc⟩
  obtain ⟨key⟩ := valueUnique rawLeast selected aux ![y]
    ⟨Derivation.conjunctionRight lc⟩ ⟨Derivation.conjunctionRight rc⟩
  obtain ⟨tag,fields⟩ := termReports (body := B) (Γ := Γ) dom altCod head a'
  have shape := headTransport termShape (suc z) aux selected Fin.elim0 ⟨symm key⟩ tag
  have exactHead := headTransport (field 2) head aux selected Fin.elim0 ⟨symm key⟩ fields.2.2.1
  exact ⟨hc,ht,⟨key⟩,shape,exactHead⟩

#print axioms exact_OpenAtomicAppliedLeastShape
end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicAppliedLeastShapeProof
