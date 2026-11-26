module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootPayloadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootPayloadProof (exact_OpenLiteralRootPayload)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelope (nodeGood field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports packedBody)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrame
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Exact original tests, on the original unchanged source/witness/target
tape. In particular matching is on the raw argument, not just its class. -/
structure Checks (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (xs : Fin 3 → OTerm α) : Prop where
  witness : D B Γ (bit (onRaw witnessShape 1) xs)
  source : D B Γ (bit (onRaw termShape 0) xs)
  target : D B Γ (bit (onRaw termShape 2) xs)
  dom : D B Γ (bit (sameSlot 0) xs)
  cod : D B Γ (bit (sameSlot 1) xs)
  arg : D B Γ (bit (sameSlot 3) xs)

theorem guardChecks (xs : Fin 3 → OTerm α) (held : D B Γ (bit frameGood xs)) :
    Checks B Γ xs := by
  unfold frameGood at held
  obtain ⟨r₀⟩ := conjunctionRecover _ _ xs held
  obtain ⟨r₁⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight r₀⟩
  obtain ⟨r₂⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight r₁⟩
  obtain ⟨r₃⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight r₂⟩
  obtain ⟨r₄⟩ := conjunctionRecover _ _ xs ⟨Derivation.conjunctionRight r₃⟩
  exact ⟨⟨Derivation.conjunctionLeft r₀⟩,⟨Derivation.conjunctionLeft r₁⟩,
    ⟨Derivation.conjunctionLeft r₂⟩,⟨Derivation.conjunctionLeft r₃⟩,
    ⟨Derivation.conjunctionLeft r₄⟩,⟨Derivation.conjunctionRight r₄⟩⟩

theorem moveBit {β : Type} (p : Program 3) (q w r : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (h : D B Γ (bit p ![q,w,r])) :
    D B Δ (bit p ![q.relabel j,w.relabel j,r.relabel j]) := by
  have moved := renameInto h j Δ keep
  simpa only [bit,programRename,tripleInputsRename,sucRelabel,zRelabel] using moved

theorem moveChecks {β : Type} (q w r : OTerm α) (j : α → β)
    (Δ : List (Formula β)) (keep : ∀ f ∈ Γ, f.relabel j ∈ Δ)
    (h : Checks B Γ ![q,w,r]) :
    Checks B Δ ![q.relabel j,w.relabel j,r.relabel j] :=
  ⟨moveBit _ q w r j Δ keep h.witness,moveBit _ q w r j Δ keep h.source,
    moveBit _ q w r j Δ keep h.target,moveBit _ q w r j Δ keep h.dom,
    moveBit _ q w r j Δ keep h.cod,moveBit _ q w r j Δ keep h.arg⟩

theorem nodeAtCases (tag arity : Nat) (i : Fin 3) (xs : Fin 3 → OTerm α)
    (goal : Formula α)
    (held : D B Γ (bit (onRaw (nodeGood (literal 1 tag) arity) i) xs))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (values : List (OTerm β)),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) → values.length = arity →
      D B Δ (eqn ((xs i).relabel j) (rawCons (numeral tag) (packedBody values))) →
      Reports B Δ ((xs i).relabel j) cellTail values → D B Δ (goal.relabel j)) :
    D B Γ goal := by
  let test := nodeGood (literal 1 tag) arity
  have uv : D B Γ (unary test (suc z) (xs i)) := by
    apply compositionRecover test (fun _ : Fin 1 => .projection i) (suc z) xs ![xs i] held
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue i xs
  let t := xs i
  have eq : NumberedWindowInternalLiteralRootDispatchNumericProof.guard tag arity = onRaw test 1 := by
    unfold NumberedWindowInternalLiteralRootDispatchNumericProof.guard onRaw
    congr 1
    funext k
    obtain rfl := Fin.eq_zero k
    rfl
  have ready : D B Γ (bit (NumberedWindowInternalLiteralRootDispatchNumericProof.guard tag arity) ![t,t,t]) := by
    rw [eq]
    exact onTape test 1 (suc z) ![t,t,t] uv
  exact exact_OpenLiteralRootPayload tag arity t t t goal ready next

theorem equalityAt (xs : Fin 3 → OTerm α) (n : Nat) (a b : OTerm α)
    (left : D B Γ (programGraph (frameSlot n 0) a xs))
    (right : D B Γ (programGraph (frameSlot n 2) b xs))
    (held : D B Γ (bit (sameSlot n) xs)) : D B Γ (eqn a b) := by
  apply equalityOfAcceptance
  apply compositionRecover equalityTest ![frameSlot n 0,frameSlot n 2] (suc z) xs ![a,b] held
  intro k
  exact Fin.cases left (Fin.cases right (fun e => Fin.elim0 e)) k

#print axioms guardChecks
#print axioms nodeAtCases
#print axioms equalityAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
