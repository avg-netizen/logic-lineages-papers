module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootPayloadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressDecodeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood rawLeast)
open NumberedWindowInternalAtomicRefinement (atomSource storedTypeFits)
open NumberedWindowInternalSparsePathEnvelope (nodeGood applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary unaryRename)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalLiteralRootDispatchNumericProof (guard)
open NumberedWindowInternalLiteralRootDispatchOpenProof (bit)
open NumberedWindowInternalLiteralRootPayloadProof (exact_OpenLiteralRootPayload)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Adapt any actual unary node check to the same literal selector
parser used at root dispatch. No numerical decoding theorem enters. -/
theorem nodeAsGuard (tag arity : Nat) (x : OTerm α)
    (h : D B Γ (unary (nodeGood (literal 1 tag) arity) (suc z) x)) :
    D B Γ (bit (guard tag arity) ![z,x,z]) := by
  apply compositionValue (nodeGood (literal 1 tag) arity) ![.projection 1] (suc z) ![z,x,z] ![x] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 ![z,x,z]

/-- Reverse the outer atom test: retain the address's three physical
fields and the actual inner constructor and stored-type checks.
The context and requested type are not guessed from a raw numeral. -/
theorem exact_OpenLiteralAtomicAddressDecode (tag arity : Nat) (x : OTerm α)
    (goal : Formula α)
    (h : D B Γ (programGraph (atomSource tag arity) (suc z) ![x]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c t k : OTerm β),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) → D B Δ (addressReport (x.relabel j) c t k) →
      D B Δ (unary (nodeGood (literal 1 tag) arity) (suc z) k) →
      D B Δ (unary storedTypeFits (suc z) (x.relabel j)) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  let kind := nodeGood (literal 1 tag) arity
  let inner := applyUnary kind rawLeast
  have unfoldTest : D B Γ (programGraph
      (conjunction addressGood (conjunction inner storedTypeFits)) (suc z) ![x]) := by
    unfold atomSource at h
    rw [exact_DispatchControlAST.2.2.2.2.2,exact_DispatchControlAST.2.2.2.2.2] at h
    exact h
  obtain ⟨pieces⟩ := conjunctionRecover addressGood (conjunction inner storedTypeFits) ![x] unfoldTest
  have outer : D B Γ (unary addressGood (suc z) x) := ⟨Derivation.conjunctionLeft pieces⟩
  obtain ⟨checks⟩ := conjunctionRecover inner storedTypeFits ![x] ⟨Derivation.conjunctionRight pieces⟩
  have raw : D B Γ (unary inner (suc z) x) := ⟨Derivation.conjunctionLeft checks⟩
  have fit : D B Γ (unary storedTypeFits (suc z) x) := ⟨Derivation.conjunctionRight checks⟩
  apply exact_OpenLiteralRootPayload 3 3 z x z goal (nodeAsGuard 3 3 x outer)
  intro β j Δ fs keep size _ fields
  rcases fs with _ | ⟨c,_ | ⟨t,_ | ⟨k,_ | ⟨d,rest⟩⟩⟩⟩ <;> simp at size
  have shell := renameInto outer j Δ keep
  have shape := renameInto raw j Δ keep
  have compare := renameInto fit j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at shell shape compare
  obtain ⟨good⟩ := shell
  obtain ⟨hc⟩ := fields.1
  obtain ⟨ht⟩ := fields.2.1
  obtain ⟨hk⟩ := fields.2.2.1
  have report : D B Δ (addressReport (x.relabel j) c t k) :=
    ⟨Derivation.conjunctionIntroduction good (Derivation.conjunctionIntroduction hc
      (Derivation.conjunctionIntroduction ht hk))⟩
  have atom := takeUnary kind rawLeast (suc z) (x.relabel j) k shape ⟨hk⟩
  exact use β j Δ c t k keep report atom compare

#print axioms nodeAsGuard
#print axioms exact_OpenLiteralAtomicAddressDecode
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressDecodeProof
