module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankNeutralReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralForwardCoordinatesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankOpenSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankNeutralClosureProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalRankMeasuredExchange (rankedExchange)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralRankNeutralReportProof
open NumberedWindowInternalLiteralForwardCoordinatesProof
open NumberedWindowInternalLiteralApplicationRowsProof (exact_OpenLiteralApplicationRows)
open NumberedWindowInternalTransparentAuxRankTargets (auxRank)
open NumberedWindowInternalTransparentAuxRankOpenSuccessorProof (exact_OpenTransparentAuxRankSuccessorIntro)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atRank (C W : Program 3) (s : Settings) (g : Program 1) (D₀ : Program 2)
    (f y ctx dom cod fn arg chosen : OTerm α) :
    let H := auxRank g
    let X := rankedExchange C s H D₀
    D B Γ (addressReport f ctx (rawCons dom cod) fn) →
    D B Γ (atom (rankNeutral H) f) →
    D B Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod fn arg) chosen) →
    D B Γ (eqn y (addressTerm ctx cod chosen)) →
    D B Γ (atom (rankNeutral H) y) := by
  intro H X addr source output eq
  apply optionGraphCases H ![fn] _
  · intro β j Δ keep absent
    rw [atomRename]
    rw [unaryInputsRename] at absent
    have a := renameInto addr j Δ keep
    rw [addressReportRename,rawConsRename] at a
    have n := renameInto source j Δ keep
    rw [atomRename] at n
    obtain ⟨impossible⟩ := exact_OpenRankNeutralRejectsZero H (f.relabel j) (ctx.relabel j)
      (rawCons (dom.relabel j) (cod.relabel j)) (fn.relabel j) a n absent
    exact ⟨Derivation.explosion impossible⟩
  · intro β j Δ pred keep on
    rw [atomRename]
    rw [unaryInputsRename] at on
    have least := renameInto output j Δ keep
    rw [leastRename,auxiliaryRename] at least
    have emitted := renameInto eq j Δ keep
    rw [eqnRelabel,renameAddress] at emitted
    let c := ctx.relabel j
    let d := dom.relabel j
    let t := cod.relabel j
    let f' := fn.relabel j
    let u := arg.relabel j
    let k := chosen.relabel j
    have inner := exact_OpenTransparentAuxRankSuccessorIntro g B β Δ d t f' u pred on
    have carried := exact_OpenSelectedRank C W s H D₀ c t (auxiliaryTerm d t f' u) k (suc (suc pred)) least inner
    exact exact_OpenRankNeutralFromRaw H (y.relabel j) c t k (suc pred)
      (exact_OpenLiteralReportedAddress (y.relabel j) c t k emitted) carried

/-- An actual accepted application of a positive-rank neutral
function has a positive-rank neutral result on the same plain least
used by the calibrated rank forward theorem. -/
theorem exact_OpenRankNeutralApplication (C W : Program 3) (s : Settings) (g : Program 1)
    (D₀ : Program 2) (i : Program 1) (f u out : OTerm α) :
    let H := auxRank g
    let X := rankedExchange C s H D₀
    let L := packedLeastProgram C X W s
    D B Γ (atom (rankNeutral H) f) →
    D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,out]) →
    D B Γ (atom (rankNeutral H) out) := by
  intro H X L source accepted
  apply exact_OpenLiteralApplicationRows i L f u out _ accepted
  intro β j Δ ctx ty dom cod fn arg k keep _ _ coords yes eq
  rw [atomRename]
  have n := renameInto source j Δ keep
  rw [atomRename] at n
  obtain ⟨a,_,_⟩ := exact_OpenParsedOperandAddresses (f.relabel j) (u.relabel j) ctx ty dom cod fn arg coords
  exact atRank C W s g D₀ (f.relabel j) (out.relabel j) ctx dom cod fn arg k a n yes eq

#print axioms exact_OpenRankNeutralApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRankNeutralClosureProof
