module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressThinDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalAcceptance (conjunction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawContext rawResult rawLeast)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary takeUnary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem fields (q ctx ty k : OTerm α) (d : Derivation body Γ (addressReport q ctx ty k)) :
    ∀ i : Fin 3, Nonempty (Derivation body Γ (unary
      ((![rawContext,rawResult,rawLeast] : Fin 3 → Program 1) i) ((![ctx,ty,k] : Fin 3 → OTerm α) i) q)) := by
  have r := Derivation.conjunctionRight d
  intro i
  exact Fin.cases ⟨Derivation.conjunctionLeft r⟩
    (Fin.cases ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight r)⟩
      (Fin.cases ⟨Derivation.conjunctionRight (Derivation.conjunctionRight r)⟩ (fun e => Fin.elim0 e))) i

theorem reported : ExactReportedAddressScalar := by
  intro cv tv W least body α Γ q ctx ty k guards
  let A := addressReport q ctx ty k
  let Δ := A :: Γ
  let i := addressScalar cv tv W least
  let hit := unary i (suc z) q
  let g := canonicalCoordinates W least
  let ac := applyUnary cv rawContext
  let atype := applyUnary tv rawResult
  have witness : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have toFields : Nonempty (Derivation body (hit :: Δ) guards) := by
    have d := addHyp witness hit
    have read := fields q ctx ty k d
    obtain ⟨part⟩ := conjunctionRecover (shapeChecks cv tv) (coordinateCall W least) ![q]
      (body := body) (Gamma := hit :: Δ) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨shell⟩ := conjunctionRecover addressGood (conjunction ac atype) ![q] ⟨Derivation.conjunctionLeft part⟩
    obtain ⟨tests⟩ := conjunctionRecover ac atype ![q] ⟨Derivation.conjunctionRight shell⟩
    obtain ⟨c⟩ := takeUnary cv rawContext (suc z) q ctx ⟨Derivation.conjunctionLeft tests⟩ (read 0)
    obtain ⟨t⟩ := takeUnary tv rawResult (suc z) q ty ⟨Derivation.conjunctionRight tests⟩ (read 1)
    obtain ⟨canonical⟩ := compositionRecover g ![rawContext,rawResult,rawLeast] (suc z) ![q] ![ctx,ty,k]
      ⟨Derivation.conjunctionRight part⟩ read
    exact ⟨Derivation.conjunctionIntroduction c (Derivation.conjunctionIntroduction t canonical)⟩
  have fromFields : Nonempty (Derivation body (guards :: Δ) hit) := by
    have d := addHyp witness guards
    have read := fields q ctx ty k d
    have data : Derivation body (guards :: Δ) guards := Derivation.hypothesis List.mem_cons_self
    have c := makeUnary cv rawContext (suc z) q ctx ⟨Derivation.conjunctionLeft data⟩ (read 0)
    have t := makeUnary tv rawResult (suc z) q ty ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight data)⟩ (read 1)
    have shell := conjunctionAccept addressGood (conjunction ac atype) ![q] ⟨Derivation.conjunctionLeft d⟩
      (conjunctionAccept ac atype ![q] c t)
    have canonical := compositionValue g ![rawContext,rawResult,rawLeast] (suc z) ![q] ![ctx,ty,k]
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight data)⟩ read
    exact conjunctionAccept (shapeChecks cv tv) (coordinateCall W least) ![q] shell canonical
  obtain ⟨toFields⟩ := toFields
  obtain ⟨fromFields⟩ := fromFields
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction toFields) (Derivation.implicationIntroduction fromFields))⟩
#print axioms reported
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressFieldsThinProof
