module
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginalApplicationFormationInterfaceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverCombinedRestrictedFormationTargets (thinFormation)
open NumberedWindowInternalMeasuredUnrestrictedRoundApplicationProof (ParentWindowsAt)

def OriginalParentClosureAt (W : Program 3) (B : Positive (Fin 1)) {α : Type}
    (Γ : List (Formula α)) (ctx dom cod arg : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (f : OTerm β),
    (∀ p ∈ Γ, p.relabel j ∈ Δ) →
    Nonempty (Derivation B Δ (windowAt W (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) f)) →
    Nonempty (Derivation B Δ
      (windowAt W (ctx.relabel j) (cod.relabel j) (auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j))))

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Genuine single-function window formation supplies both actual
application-side reports at every real typed edge. No assumption on the
identities or ranking of the two raw representatives is used. -/
theorem exact_ParentWindowsFromOriginalClosure (W : Program 3) (X : Program 2)
    (ctx dom cod arg : OTerm α) (close : OriginalParentClosureAt W B Γ ctx dom cod arg) :
    ParentWindowsAt (edge4 X W) W B Γ ctx dom cod arg := by
  intro β j Δ f g keep edge
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge X W B β Δ (ctx.relabel j)
    (rawCons (dom.relabel j) (cod.relabel j)) f g
  obtain ⟨edge⟩ := edge
  let checked := Derivation.implicationElimination (Derivation.conjunctionLeft law) edge
  let both := Derivation.conjunctionRight checked
  exact ⟨close β j Δ f keep ⟨Derivation.conjunctionLeft both⟩,
    close β j Δ g keep ⟨Derivation.conjunctionRight both⟩⟩

/-- Install that same actual original formation law as the original
arithmetic universal formula used by the raw fixed-argument hop maps. -/
theorem exact_OriginalThinFormationFromParentClosure (W : Program 3) (ctx dom cod arg : OTerm α)
    (close : OriginalParentClosureAt W B Γ ctx dom cod arg) :
    Nonempty (Derivation B Γ (thinFormation W ctx dom cod arg)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f
  let Δ := A :: Γ.map (fun p => p.relabel j)
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have fn : Nonempty (Derivation B Δ (windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  rw [rawConsRename] at fn
  obtain ⟨parent⟩ := close (α ⊕ Fin 1) j Δ f keep fn
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction parent)⟩

#print axioms exact_ParentWindowsFromOriginalClosure
#print axioms exact_OriginalThinFormationFromParentClosure
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginalApplicationFormationInterfaceProof
