module

public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename equalEqn)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalStrictAuxWindowHeaderTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveWindow (W : Program 3) (ctx ty other raw key : OTerm α)
    (types : Nonempty (Derivation body Γ (eqn ty other)))
    (keys : Nonempty (Derivation body Γ (eqn raw key)))
    (actual : Nonempty (Derivation body Γ (windowGraph W ctx ty raw))) :
    Nonempty (Derivation body Γ (windowGraph W ctx other key)) := by
  have self : Nonempty (Derivation body Γ (equal ctx ctx)) := by rw [equalEqn]; exact ⟨refl ctx⟩
  have sameTy : Nonempty (Derivation body Γ (equal ty other)) := by rw [equalEqn]; exact types
  have sameKey : Nonempty (Derivation body Γ (equal raw key)) := by rw [equalEqn]; exact keys
  apply graphInputTransport body α 3 Γ (OrdinaryArithmetic.graphFormula W) (suc z)
    ![ctx,ty,raw] ![ctx,other,key] _ actual
  intro i
  exact Fin.cases self (Fin.cases sameTy (Fin.cases sameKey (fun k => Fin.elim0 k))) i

theorem exact_OpenStrictAuxWindowAtHeader : ExactOpenStrictAuxWindowAtHeader := by
  intro base T body α Γ ctx ty raw goal parent header next
  apply exact_OpenCoverHeaderFields 6 4 body α Γ raw goal header
  intro β j Δ fields keep len reports packing
  rcases fields with _ | ⟨dom,_ | ⟨cod,_ | ⟨fn,_ | ⟨arg,_ | ⟨extra,rest⟩⟩⟩⟩⟩ <;> simp at len
  let W := strictAuxWindow base T
  let c := ctx.relabel j
  let t := ty.relabel j
  let q := raw.relabel j
  let key := auxiliaryTerm dom cod fn arg
  change Nonempty (Derivation body Δ (eqn q key)) at packing
  have actual := renameInto parent j Δ keep
  simp only [windowGraph,programRename,tripleInputsRename,sucRelabel,zRelabel] at actual
  have literal := moveWindow W c t t q key ⟨refl t⟩ packing actual
  have type := exact_OpenStrictAuxWindowResultType base T body β Δ c t dom cod fn arg literal
  have sameCod := moveWindow W c t cod key key type ⟨refl key⟩ literal
  have children := exact_OpenStrictAuxWindowParent base T body β Δ c dom cod fn arg sameCod
  exact next β j Δ dom cod fn arg keep reports packing type children

#print axioms exact_OpenStrictAuxWindowAtHeader

end LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowHeaderProof
