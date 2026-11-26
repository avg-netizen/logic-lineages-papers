module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportDomainProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique projectionValue compositionValue)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePackedLeast (contextOption minimumAtMembers)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverRename coverBinder)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)

private theorem shareContext (ctx ty a b payload : OTerm α)
    (src : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,a]))) :
    Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,b])) := by
  have project (seed : OTerm α) (i : Fin 1) : Nonempty (Derivation body Γ
      (programGraph (.projection 0) ((![ctx] : Fin 1 → OTerm α) i) ![ctx,ty,seed])) := by
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 ![ctx,ty,seed]
  have actual := compositionRecover parser (fun _ : Fin 1 => .projection (0 : Fin 3)) (suc payload)
    ![ctx,ty,a] ![ctx] src (project a)
  exact compositionValue parser (fun _ : Fin 1 => .projection (0 : Fin 3)) (suc payload)
    ![ctx,ty,b] ![ctx] actual (project b)

private theorem atParsed (ctx ty seed payload : OTerm α)
    (parsed : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (own : Nonempty (Derivation body Γ (occursInCover C s seed seed))) :
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty seed)) := by
  obtain ⟨own⟩ := own
  let j : α → α ⊕ Fin 1 := Sum.inl
  let Δ := coverBinder C s seed seed :: Γ.map weaken
  have h : Derivation body Δ (coverBinder C s seed seed) := Derivation.hypothesis List.mem_cons_self
  have pc := renameInto parsed j Δ (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  simp only [programRename,sucRelabel,tripleInputsRename] at pc
  obtain ⟨rule⟩ := NumberedWindowInternalSparsePackedDomainChecks.exact_PackedDomain C X W s body _ Δ
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) (payload.relabel j) (.var (.inr 0))
  obtain ⟨pc⟩ := pc
  have eqv := Derivation.implicationElimination rule (Derivation.conjunctionIntroduction pc (Derivation.conjunctionLeft h))
  have done : Derivation body Δ (weaken (hasLeast C X W s ctx ty seed)) := by
    change Derivation body Δ ((hasLeast C X W s ctx ty seed).relabel j)
    rw [hasRename]
    exact Derivation.implicationElimination (Derivation.conjunctionRight eqv) (Derivation.conjunctionRight h)
  exact ⟨Derivation.existentialElimination own done⟩

theorem targetExists (ctx ty a b x : OTerm α)
    (source : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty a x)))
    (target : Nonempty (Derivation body Γ (occursInCover C s b b))) :
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty b)) := by
  apply optionGraphCases contextOption (![ctx,ty,a] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have run := renameInto source j Δ keep
    rw [leastRename] at run
    let xs := ![ctx.relabel j,ty.relabel j,a.relabel j]
    have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
      (suc (x.relabel j)) xs zero run
    obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc (x.relabel j)) z xs lost (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename] at parsed
    rw [hasRename]
    have member := renameInto target j Δ keep
    rw [coverRename] at member
    exact atParsed C X W s _ _ _ _ (shareContext _ _ _ (b.relabel j) payload parsed) member
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseExchangeTransportDomainProof
