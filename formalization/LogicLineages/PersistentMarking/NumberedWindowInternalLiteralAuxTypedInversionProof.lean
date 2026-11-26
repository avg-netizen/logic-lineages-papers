module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunInversionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootPayloadProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxTypedInversionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalLiteralRootDispatchOpenProof
  (D bit exact_OpenLiteralRootCaseElimination)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root shapes)
open NumberedWindowInternalLiteralRootPayloadProof (exact_OpenLiteralRootPayload)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralAuxRunChildProof (ChildTerminal)
open NumberedWindowInternalLiteralAuxRunInversionProof (exact_OpenAuxiliaryRunInversion)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Both actual outer endpoint guards are recovered, and either the
original root program's exact selected leaf or genuine function-side
context is opened. No numerical reflection into a derivation is used. -/
theorem exact_OpenTypedAuxiliaryInversion (leaf : Nat → Program 3) (other window : Program 3)
    (syntaxCheck : Program 1) (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (held : D B Γ (programGraph (typedRaw5 (root leaf) (auxiliaryFallback other) window syntaxCheck)
      (suc z) ![ctx,ty,q,w,r]))
    (rootCase : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) →
      ∀ tag arity, (tag,arity) ∈ shapes →
        ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
          (∀ f ∈ Γ, f.relabel j ∈ Δ) →
          D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
          D B Δ (bit (NumberedWindowInternalLiteralRootDispatchNumericProof.guard tag arity)
            ![q.relabel j,payload,r.relabel j]) →
          D B Δ (bit (leaf tag) ![q.relabel j,payload,r.relabel j]) →
          D B Δ (goal.relabel j))
    (functionCase : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (dom cod fn arg child dom' cod' dest arg' : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
          dom cod fn arg child dom' cod' dest arg' →
        D B Δ (ChildTerminal (root leaf) other fn child dest) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  obtain ⟨move⟩ := exact_OpenTypedRaw5 B (root leaf) (auxiliaryFallback other)
    window syntaxCheck α Γ ctx ty q w r
  obtain ⟨run⟩ := held
  have parts := Derivation.implicationElimination (Derivation.conjunctionLeft move) run
  have guards : D B Γ (liftedEndpointGuards window syntaxCheck ctx ty q r) :=
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft (Derivation.conjunctionLeft parts))
      (Derivation.conjunctionRight parts)⟩
  have raw : D B Γ (bit (NumberedWindowInternalSparseRawRun.ownRun (root leaf) (auxiliaryFallback other))
      ![q,w,r]) := ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft parts)⟩
  apply exact_OpenAuxiliaryRunInversion (root leaf) other q w r goal aux raw
  · intro β j Δ payload keep wit accepted
    apply exact_OpenLiteralRootCaseElimination leaf ![q.relabel j,payload,r.relabel j]
      (goal.relabel j) accepted
    intro tag arity know Ω stay branch ruled
    have w' := wit.map (Derivation.weakening (fun f h => stay f h))
    exact rootCase guards tag arity know β j Ω payload (fun f h => stay _ (keep f h)) w' branch ruled
  · exact functionCase guards

#print axioms exact_OpenTypedAuxiliaryInversion

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxTypedInversionProof
