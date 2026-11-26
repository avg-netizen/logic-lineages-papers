module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodec (consCode headCode tailCode)
open ID1Completion.InternalListCodecSupportProof (consDestruction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets

abbrev call6 {α : Type} (k prior c ty start cert : OTerm α) : Fin 6 → OTerm α :=
  ![k,prior,c,ty,start,cert]

theorem callRename {α β : Type} (k prior c ty start cert : OTerm α) (j : α → β) :
    (fun i => (call6 k prior c ty start cert i).relabel j) =
      call6 (k.relabel j) (prior.relabel j) (c.relabel j)
        (ty.relabel j) (start.relabel j) (cert.relabel j) := by
  funext i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m =>
    Fin.cases ?_ (fun n => Fin.cases ?_ (fun o => Fin.cases ?_ (fun u => Fin.elim0 u) o) n) m) l) k) i <;>
    rfl

theorem selectedRename {α β : Type} (p : Program 6) (o k prior c ty start cert : OTerm α) (j : α → β) :
    (programGraph p o (call6 k prior c ty start cert)).relabel j =
      programGraph p (o.relabel j) (call6 (k.relabel j) (prior.relabel j) (c.relabel j)
        (ty.relabel j) (start.relabel j) (cert.relabel j)) := by
  rw [programRename,callRename]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem moveSelected {β : Type} (j : α → β) (Δ : List (Formula β))
    (hJ : ∀ p ∈ Γ, p.relabel j ∈ Δ) (p : Program 6) (o k prior c ty start cert : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph p o (call6 k prior c ty start cert)))) :
    Nonempty (Derivation body Δ (programGraph p (o.relabel j)
      (call6 (k.relabel j) (prior.relabel j) (c.relabel j) (ty.relabel j)
        (start.relabel j) (cert.relabel j)))) := by
  have moved := renameInto h j Δ hJ
  rw [selectedRename] at moved
  exact moved

private theorem cutStateAt (p : Program 1) (v k prior c ty start cert : OTerm α)
    (h : Nonempty (Derivation body Γ (unary p v prior))) :
    Nonempty (Derivation body Γ (programGraph (.composition p (fun _ : Fin 1 => .projection 1))
      v (call6 k prior c ty start cert))) := by
  let args := call6 k prior c ty start cert
  apply compositionValue p (fun _ : Fin 1 => .projection 1) v args ![prior] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (1 : Fin 6) args

theorem stateParts (cursor current k prior c ty start cert : OTerm α)
    (h : Nonempty (Derivation body Γ (scratchGraph prior cursor current))) :
    let args := call6 k prior c ty start cert
    Nonempty (Derivation body Γ (programGraph scratchCursor cursor args)) ∧
    Nonempty (Derivation body Γ (programGraph scratchCurrent current args)) := by
  obtain ⟨bits⟩ := consDestruction prior cursor current h
  exact ⟨cutStateAt headCode cursor k prior c ty start cert ⟨Derivation.conjunctionLeft bits⟩,
    cutStateAt tailCode current k prior c ty start cert
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight bits)⟩⟩

theorem atCursor (p : Program 1) (o cursor : OTerm α) (args : Fin 6 → OTerm α)
    (h : Nonempty (Derivation body Γ (unary p o cursor)))
    (hCursor : Nonempty (Derivation body Γ (programGraph scratchCursor cursor args))) :
    Nonempty (Derivation body Γ (programGraph (onCursor p) o args)) := by
  apply compositionValue p (fun _ : Fin 1 => scratchCursor) o args ![cursor] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact hCursor

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof
