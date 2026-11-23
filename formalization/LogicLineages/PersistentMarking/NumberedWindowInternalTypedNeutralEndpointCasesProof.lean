module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalTypedNeutralEndpointCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalProbeTargets (OTerm typeCode)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalFreshProbeParsedTypedArrowFieldsProof (actualArrowFields)
open NumberedWindowInternalAtomicApplicationShapeObjectTargets (literalApplicationShape auxAddressTerm)

/-- Exact report on held argument/result, not their typing or I. Keep
the argument's own least raw a distinct from emitted a'. -/
structure EndpointReports (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (σ τ : ProbeTy) (ctx head arg out dom cod a a' : OTerm α) : Prop where
  domain : Nonempty (Derivation B Γ (equal dom (numeral (typeCode σ))))
  codomain : Nonempty (Derivation B Γ (equal cod (numeral (typeCode τ))))
  argument : Nonempty (Derivation B Γ (equal arg (addressTerm ctx dom a)))
  endpoint : Nonempty (Derivation B Γ (equal out (auxAddressTerm ctx dom cod head a')))

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Untelescope the actual shape packet and align its stored arrow
coordinates to a literal type using object cons injectivity, not
evaluation of an open term or a semantic typing premise. -/
theorem exact_OpenTypedNeutralEndpointCases (σ τ : ProbeTy) (ctx ty head arg out : OTerm α)
    (declared : Nonempty (Derivation B Γ (equal ty (numeral (typeCode (.arrow σ τ))))))
    (held : Nonempty (Derivation B Γ (literalApplicationShape ctx ty head arg out)))
    (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (dom cod a a' : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      EndpointReports B Δ σ τ (ctx.relabel j) (head.relabel j) (arg.relabel j) (out.relabel j)
        dom cod a a' →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  let β := α ⊕ Fin 4
  let j : α → β := Sum.inl
  let dom : OTerm β := .var (.inr 0)
  let cod : OTerm β := .var (.inr 1)
  let a : OTerm β := .var (.inr 2)
  let a' : OTerm β := .var (.inr 3)
  let matrix := equal (ty.relabel j) (consTerm dom cod) ⊓
    (equal (arg.relabel j) (addressTerm (ctx.relabel j) dom a) ⊓
      equal (out.relabel j) (auxAddressTerm (ctx.relabel j) dom cod (head.relabel j) a'))
  apply actualFiniteExistentialElimination B α 4 Γ matrix goal held
  let Δ := matrix :: Γ.map (fun f => f.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ :=
    fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have same := renameInto declared j Δ keep
  have known : Nonempty (Derivation B Δ (equal (ty.relabel j) (numeral (typeCode (.arrow σ τ))))) := by
    simpa only [equalEqn,eqnRelabel,numeralRename] using same
  have faces : Derivation B Δ matrix := Derivation.hypothesis List.mem_cons_self
  have q := Derivation.conjunctionRight faces
  obtain ⟨fields⟩ := actualArrowFields σ τ (ty.relabel j) dom cod known ⟨Derivation.conjunctionLeft faces⟩
  exact next β j Δ dom cod a a' keep
    ⟨⟨Derivation.conjunctionLeft fields⟩,⟨Derivation.conjunctionRight fields⟩,
      ⟨Derivation.conjunctionLeft q⟩,⟨Derivation.conjunctionRight q⟩⟩

#print axioms exact_OpenTypedNeutralEndpointCases
end LogicLineages.PersistentMarking.NumberedWindowInternalTypedNeutralEndpointCasesProof
