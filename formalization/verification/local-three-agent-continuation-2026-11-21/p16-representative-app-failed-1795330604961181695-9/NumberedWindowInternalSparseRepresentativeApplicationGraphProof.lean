module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalBinderTransportProof (actualRelabelSubstitution)
open ID1Completion.InternalBinderTransportSyntaxProof (formulaSubstVar)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseApplicationOutputCore (selectedLeast seed)
open NumberedWindowInternalSparseApplicationOutputCoreEmitterProof (objectTape seedGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRepresentativeApplicationTargets
attribute [local irreducible] programGraph

theorem observerGraph : ExactApplicationObservation := by
  intro least body α Γ ctx dom cod arg f out
  let xs : Fin 5 → OTerm α := ![f,ctx,dom,cod,arg]
  let ys := objectTape ctx dom cod f arg f
  let zs : Fin 3 → OTerm α := ![ctx,cod,auxiliaryTerm dom cod f arg]
  let route : Fin 6 → Program 5 := ![.projection 1,.projection 2,.projection 3,.projection 0,.projection 4,.projection 0]
  let values : Fin 3 → Program 6 := ![.projection 0,.projection 2,seed]
  have routed (i : Fin 6) : Nonempty (Derivation body Γ (programGraph (route i) (ys i) xs)) :=
    Fin.cases (projectionValue 1 xs) (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 4 xs) (Fin.cases (projectionValue 0 xs)
        (fun e => Fin.elim0 e)))))) i
  have emitted (i : Fin 3) : Nonempty (Derivation body Γ (programGraph (values i) (zs i) ys)) :=
    Fin.cases (projectionValue 0 ys) (Fin.cases (projectionValue 2 ys) (Fin.cases
      (seedGraph ctx dom cod f arg f) (fun e => Fin.elim0 e))) i
  constructor
  · intro h
    exact compositionRecover least values out ys zs (compositionRecover (selectedLeast least) route out xs ys h routed) emitted
  · intro h
    exact compositionValue (selectedLeast least) route out xs ys (compositionValue least values out ys zs h emitted) routed

/-- Use the two fresh variables from universal introduction as the arguments
of an already established open two-variable condition. -/
theorem openBlock {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (p : Formula (α ⊕ Fin 2)) (h : Nonempty (Derivation body Γ (allBlock p))) :
    Nonempty (Derivation body (Γ.map (fun q => q.relabel Sum.inl)) p) := by
  let j : α → α ⊕ Fin 2 := Sum.inl
  let Δ := Γ.map (fun q => q.relabel j)
  have moved := renameInto h j Δ (by intro q hq; exact List.mem_map.mpr ⟨q,hq,rfl⟩)
  rw [allBlockRename] at moved
  obtain ⟨out⟩ := ID1Completion.InternalClosedProgramsBindingProof.elimination body _ 2 Δ
    (p.relabel (Sum.map j id)) (fun i => .var (.inr i)) moved
  rw [actualRelabelSubstitution] at out
  have identity : (fun x : α ⊕ Fin 2 => Sum.elim Term.var (fun i => Term.var (Sum.inr i)) (Sum.map j id x)) =
      (Term.var : α ⊕ Fin 2 → Term (α ⊕ Fin 2)) := by
    funext x
    cases x <;> rfl
  rw [identity,formulaSubstVar] at out
  exact ⟨out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationGraphProof
