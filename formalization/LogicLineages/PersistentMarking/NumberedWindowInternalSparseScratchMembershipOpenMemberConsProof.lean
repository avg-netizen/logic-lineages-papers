module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenRowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consValue)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembership
open NumberedWindowInternalSparseScratchMembershipTargets
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenRowProof (stepHit stepKeep)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Head occurrence at the same actual cons; obtain the genuine recursive
value using original Program totality, never a default tail bit. -/
theorem headMember (code h tail k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h tail)))
    (same : Nonempty (Derivation body Γ (eqn k h))) :
    Nonempty (Derivation body Γ (memberGraph code k)) := by
  apply programCases scratchMember ![tail,k] (memberGraph code k)
  intro β j Δ previous keep observed
  rw [graphRename]
  rw [binaryInputsRename] at observed
  have hasCell := renameInto cell j Δ keep
  rw [consGraphRename] at hasCell
  have equals := renameInto same j Δ keep
  rw [eqnRelabel] at equals
  obtain ⟨he⟩ := equals
  let h' := h.relabel j
  let t' := tail.relabel j
  let k' := k.relabel j
  exact consValue memberBase memberStep (code.relabel j) h' t' previous (suc z) ![k']
    hasCell observed (stepHit h' previous k' ⟨symm he⟩)

theorem tailMember (code h tail k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h tail)))
    (member : Nonempty (Derivation body Γ (memberGraph tail k))) :
    Nonempty (Derivation body Γ (memberGraph code k)) :=
  consValue memberBase memberStep code h tail (suc z) (suc z) ![k] cell member (stepKeep h k)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
