module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAuxShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxGeneralOwnFuelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRunInversionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxThreeWaysProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawChecks

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredTypedAuxChildProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxOwnFuelCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicCoveredCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawRunRootTargets (rootWitnessTerm)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseTypedRawLiftTargets (liftedEndpointGuards)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralFunctionGuardInversionProof (Parts)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalLiteralCoveredMemoAuxRowProof (childAtWindow)
open NumberedWindowInternalLiteralCoveredTypedAuxChildProof (exact_OpenCoveredTypedFunctionChild)
open NumberedWindowInternalLiteralAuxiliaryAtomicTypedRawProof (auxiliaryAtomicTypedRaw)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicRoot atomicFallback)
open NumberedWindowInternalLiteralAtomicAuxShapeProof (exact_OpenAuxiliaryNotAtoms)
open NumberedWindowInternalLiteralAtomicFallbackDecoderProof (exact_OpenAtomicRootNonAtom)
open NumberedWindowInternalLiteralAuxGeneralOwnFuelProof (exact_OpenAtomicFunctionChildOwnFuel)
open NumberedWindowInternalLiteralAuxRunInversionProof (exact_OpenAuxiliaryRunInversion)
open NumberedWindowInternalLiteralAuxRootLeafOpenProof (exact_OpenAuxiliaryRootLeafCases)
open NumberedWindowInternalLiteralRootDispatchOpenProof (exact_OpenLiteralRootCaseElimination)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (moveBit)
open NumberedWindowInternalLiteralAuxThreeWaysProof (moveAuxInputs)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (endpointGuardsRename)
open NumberedWindowInternalSparseTypedRawChecks (exact_OpenTypedRaw5)
open NumberedWindowInternalSparseRawRun (ownRun)

def PerTickRaw (C : Program 3) (s : Settings) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
    (T V : Program 1) : Program 5 :=
  auxiliaryAtomicTypedRaw (root (leafAtAuxiliary leaf)) (fallback other) (coveredMemoWindow C s base T V) V

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The inherited function step has the exact same physically selected
raw checker as the parent, with its same-context typing guards and its
own accepting witness. The unchanged argument is a genuine typed
window report. Their own selected least programs are shown to succeed;
no quotient transport between different raw representatives is assumed. -/
theorem exact_OpenAtomicCoveredChildCases (C : Program 3) (X : Program 2) (s : Settings) (leaf : Nat → Program 3) (other : Program 3) (base : Program 2)
    (T V : Program 1) (ctx ty q w r : OTerm α) (goal : Formula α)
    (aux : D B Γ (bit sourceIsAux ![q,w,r]))
    (held : D B Γ (programGraph (PerTickRaw C s leaf other base T V) (suc z) ![ctx,ty,q,w,r]))
    (beta : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 6) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit functionLambdaHeader ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (bottom : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (payload : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        D B Δ (eqn (w.relabel j) (rootWitnessTerm payload)) →
        D B Δ (bit (leaf 7) ![q.relabel j,payload,r.relabel j]) →
        D B Δ (bit targetBottom ![q.relabel j,payload,r.relabel j]) →
        D B Δ (goal.relabel j))
    (context : D B Γ (liftedEndpointGuards (coveredMemoWindow C s base T V) V ctx ty q r) →
      ∀ (β : Type) (j : α → β) (Δ : List (Formula β))
        (dom cod fn arg child dom' cod' dest arg' : OTerm β),
        (∀ f ∈ Γ, f.relabel j ∈ Δ) →
        Parts B Δ (q.relabel j) (w.relabel j) (r.relabel j)
          dom cod fn arg child dom' cod' dest arg' →
        D B Δ (programGraph (PerTickRaw C s leaf other base T V) (suc z)
          ![ctx.relabel j,rawCons dom cod,fn,child,dest] ⊓
          (childAtWindow (coveredMemoWindow C s base T V) V (ctx.relabel j) dom arg ⊓
            (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) fn ⊓
              (hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) (rawCons dom cod) dest ⊓
                hasLeast C X (coveredMemoWindow C s base T V) s (ctx.relabel j) dom arg)))) →
        D B Δ (goal.relabel j)) : D B Γ goal := by
  let P := root (leafAtAuxiliary leaf)
  let Q := atomicRoot P
  let A := atomicFallback (fallback other)
  let W := coveredMemoWindow C s base T V
  obtain ⟨codec⟩ := exact_OpenTypedRaw5 B Q (auxiliaryFallback A) W V α Γ ctx ty q w r
  obtain ⟨call⟩ := held
  let fields := Derivation.implicationElimination (Derivation.conjunctionLeft codec) call
  have guards : D B Γ (liftedEndpointGuards W V ctx ty q r) := ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft (Derivation.conjunctionLeft fields)) (Derivation.conjunctionRight fields)⟩
  have run : D B Γ (bit (ownRun Q (auxiliaryFallback A)) ![q,w,r]) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft fields)⟩
  apply exact_OpenAuxiliaryRunInversion Q A q w r goal aux run
  · intro β j Δ payload keep witness held'
    let qs := q.relabel j
    let rs := r.relabel j
    let xs : Fin 3 → OTerm β := ![qs,payload,rs]
    have old := moveBit sourceIsAux q w r j Δ keep aux
    have hasAux := moveAuxInputs qs (w.relabel j) rs payload rs old
    obtain ⟨notAtoms⟩ := exact_OpenAuxiliaryNotAtoms qs payload rs hasAux
    have proved := exact_OpenAtomicRootNonAtom P qs payload rs (suc z) ⟨Derivation.conjunctionLeft notAtoms⟩
      ⟨Derivation.conjunctionRight notAtoms⟩ held'
    apply exact_OpenLiteralRootCaseElimination (leafAtAuxiliary leaf) xs (goal.relabel j) proved
    intro tag arity know Ω stay which got
    let retained (f : Formula α) (hf : f ∈ Γ) : f.relabel j ∈ Ω := stay _ (keep f hf)
    have hAux : D B Ω (bit sourceIsAux xs) := hasAux.map (Derivation.weakening (fun f h => stay f h))
    have wEq := witness.map (Derivation.weakening (fun f h => stay f h))
    exact exact_OpenAuxiliaryRootLeafCases leaf tag arity know xs (goal.relabel j) hAux got
      (beta guards β j Ω payload retained wEq) (bottom guards β j Ω payload retained wEq)
  · intro β j Δ dom cod fn arg child dom' cod' dest arg' keep parts terminal
    have fits := renameInto guards j Δ keep
    rw [endpointGuardsRename] at fits
    have childRun := exact_OpenAtomicFunctionChildOwnFuel Q other fn child dest terminal
    have typedChild := exact_OpenCoveredTypedFunctionChild C X s Q (auxiliaryFallback A) base T V
      (ctx.relabel j) (ty.relabel j) (q.relabel j) (w.relabel j) (r.relabel j)
      dom cod fn arg child dom' cod' dest arg' parts fits childRun
    exact context guards β j Δ dom cod fn arg child dom' cod' dest arg' keep parts typedChild

#print axioms exact_OpenAtomicCoveredChildCases
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicCoveredCasesProof
