module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressDecodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicShapeDecodeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeParsedEmitter (rawResult rawLeast)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalAtomicRefinement (atomSource storedType storedTypeFits)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparsePathEnvelope (nodeGood field)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody Reports unaryRename makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalLiteralRootPayloadProof (exact_OpenLiteralRootPayload)
open NumberedWindowInternalLiteralAtomicLeastOpenProof (D)
open NumberedWindowInternalLiteralAtomicAddressReportProof (rebuildAddress)
open NumberedWindowInternalLiteralAtomicAddressDecodeProof (nodeAsGuard exact_OpenLiteralAtomicAddressDecode)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An arbitrary successful address atom test yields the literal
constructor in a retained open context. The first raw payload field
is exactly the address's reported type, proved by the selected
stored-type equality check. No original or raw values are assumed. -/
theorem exact_OpenLiteralAtomicShapeDecode (tag rest : Nat) (x : OTerm α)
    (goal : Formula α)
    (h : D B Γ (programGraph (atomSource tag (rest+1)) (suc z) ![x]))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c t : OTerm β) (tail : List (OTerm β)),
      (∀ φ ∈ Γ, φ.relabel j ∈ Δ) → tail.length = rest →
      D B Δ (eqn (x.relabel j) (addressTerm c t (rawCons (numeral tag) (packedBody (t::tail))))) →
      D B Δ (goal.relabel j)) :
    D B Γ goal := by
  apply exact_OpenLiteralAtomicAddressDecode tag (rest+1) x goal h
  intro β j Δ c t raw keep address shell fit
  apply exact_OpenLiteralRootPayload tag (rest+1) z raw z (goal.relabel j)
    (nodeAsGuard tag (rest+1) raw shell)
  intro γ l Ω fields stay len _ selectors
  cases fields with
  | nil => simp at len
  | cons rawType tail =>
    let m := l ∘ j
    let y := (x.relabel j).relabel l
    let c' := c.relabel l
    let t' := t.relabel l
    let raw' := raw.relabel l
    have remain (φ : Formula α) (mem : φ ∈ Γ) : φ.relabel m ∈ Ω := by
      simpa only [m,formulaRelabelComposition] using stay _ (keep φ mem)
    have outer := renameInto address l Ω stay
    rw [addressReportRename] at outer
    have checked := renameInto fit l Ω stay
    simp only [unaryRename,sucRelabel,zRelabel] at checked
    have node := renameInto shell l Ω stay
    simp only [unaryRename,sucRelabel,zRelabel] at node
    obtain ⟨row⟩ := outer
    let values := Derivation.conjunctionRight (Derivation.conjunctionRight row)
    have typeReport : D B Ω (unary rawResult t' y) := ⟨Derivation.conjunctionLeft values⟩
    have leastReport : D B Ω (unary rawLeast raw' y) := ⟨Derivation.conjunctionRight values⟩
    have stored : D B Ω (unary storedType rawType y) :=
      makeUnary (field 0) rawLeast rawType y raw' selectors.1 leastReport
    unfold storedTypeFits unary at checked
    rw [exact_DispatchControlAST.2.2.2.1] at checked
    have compare := compositionRecover equalityTest
      (Fin.cons rawResult (Fin.cons storedType Fin.elim0)) (suc z) ![y]
      ![t',rawType] checked (fun i =>
        Fin.cases typeReport (Fin.cases stored (fun e => Fin.elim0 e)) i)
    obtain ⟨eq⟩ := equalityOfAcceptance t' rawType compare
    have fields' : Reports B Ω raw' cellTail (t'::tail) :=
      ⟨outputTransport (field 0) rawType t' ![raw'] ⟨symm eq⟩ selectors.1,selectors.2⟩
    have size : tail.length = rest := Nat.succ.inj len
    have selectorNode : D B Ω
        (unary (nodeGood (literal 1 tag) (t'::tail).length) (suc z) raw') := by
      simpa only [List.length_cons,size] using node
    have tagGraph : D B Ω (unary (literal 1 tag) (numeral tag) raw') := literalGraph tag ![raw']
    have same := readNode (literal 1 tag) raw' (numeral tag) (t'::tail) tagGraph selectorNode fields'
    have eqnAddress := rebuildAddress y c' t' raw' c' t' (rawCons (numeral tag) (packedBody (t'::tail)))
      ⟨row⟩ ⟨ID1Completion.InternalTagArithmeticSupportProof.refl c'⟩
      ⟨ID1Completion.InternalTagArithmeticSupportProof.refl t'⟩ same
    have reply := use γ m Ω c' t' tail remain size
      (by simpa only [y,m,Term.relabel_relabel] using eqnAddress)
    simpa only [m,formulaRelabelComposition] using reply

#print axioms exact_OpenLiteralAtomicShapeDecode
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicShapeDecodeProof
