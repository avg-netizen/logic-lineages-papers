module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedFilter (pass passGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof
  (passed memberOfPass hitGraph hitRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem passedValue (E : Program 4) (out vertices seen ctx ty k : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out vertices seen ctx ty))) :
    Nonempty (Derivation body Γ (programGraph (passed E) out
      (![vertices,seen,ctx,ty,k] : Fin 5 → OTerm α))) := by
  let xs : Fin 5 → OTerm α := ![vertices,seen,ctx,ty,k]
  apply compositionValue (pass E)
    (![.projection 0,.projection 1,.projection 2,.projection 3] : Fin 4 → Program 5)
    out xs (![vertices,seen,ctx,ty] : Fin 4 → OTerm α) run
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
      (fun noIndex => Fin.elim0 noIndex)))) i

/-- The actual pass output and its actual membership bit compose to the
literal composed program on the same physical tape. -/
theorem hitIntro (E : Program 4) (out vertices seen ctx ty k : OTerm α)
    (run : Nonempty (Derivation body Γ (passGraph E out vertices seen ctx ty)))
    (member : Nonempty (Derivation body Γ (memberGraph out k))) :
    Nonempty (Derivation body Γ (hitGraph E vertices seen ctx ty k)) := by
  let xs : Fin 5 → OTerm α := ![vertices,seen,ctx,ty,k]
  have inner := passedValue E out vertices seen ctx ty k run
  apply compositionValue scratchMember (![passed E,.projection 4] : Fin 2 → Program 5)
    (suc z) xs (![out,k] : Fin 2 → OTerm α) member
  intro i
  exact Fin.cases inner
    (Fin.cases (projectionValue 4 xs) (fun noIndex => Fin.elim0 noIndex)) i

/-- Original Program totality selects the filtered output as an object
eigenvariable; the composed graph then gives its actual membership bit. -/
theorem hitCases (E : Program 4) (vertices seen ctx ty k : OTerm α) (psi : Formula α)
    (hit : Nonempty (Derivation body Γ (hitGraph E vertices seen ctx ty k)))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ (passGraph E out (vertices.relabel j) (seen.relabel j)
        (ctx.relabel j) (ty.relabel j))) →
      Nonempty (Derivation body Δ (memberGraph out (k.relabel j))) →
      Nonempty (Derivation body Δ (psi.relabel j))) :
    Nonempty (Derivation body Γ psi) := by
  apply programCases (pass E) (![vertices,seen,ctx,ty] : Fin 4 → OTerm α) psi
  intro β j Δ out keep run
  rw [quadInputsRename] at run
  have moved := renameInto hit j Δ keep
  rw [hitRename] at moved
  let xs : Fin 5 → OTerm β :=
    ![vertices.relabel j,seen.relabel j,ctx.relabel j,ty.relabel j,k.relabel j]
  have inner := passedValue E out (vertices.relabel j) (seen.relabel j) (ctx.relabel j)
    (ty.relabel j) (k.relabel j) run
  have member : Nonempty (Derivation body Δ (memberGraph out (k.relabel j))) := by
    apply compositionRecover scratchMember (![passed E,.projection 4] : Fin 2 → Program 5)
      (suc z) xs (![out,k.relabel j] : Fin 2 → OTerm β) moved
    intro i
    exact Fin.cases inner
      (Fin.cases (projectionValue 4 xs) (fun noIndex => Fin.elim0 noIndex)) i
  exact next β j Δ out keep run member

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
