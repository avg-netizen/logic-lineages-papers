module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (emb)
open OriginalInternalAppendLookup OriginalInternalAppendLookupSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tailIntro (frontCount suffix index value suffixIndex suffixCount : OTerm alpha)
 (h : Nonempty (Derivation body Delta (tailFields frontCount suffix index value suffixIndex suffixCount))) :
 Nonempty (Derivation body Delta (Tail frontCount suffix index value)) := by
 apply InternalFiniteBlocksProof.introduction body alpha 2 Delta
   (tailMatrix frontCount suffix index value) (fun i => emb (![suffixIndex,suffixCount] i))
 rw [tailWitness]
 exact h

theorem tailCases (frontCount suffix index value : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Tail frontCount suffix index value)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (suffixIndex suffixCount : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (tailFields (frontCount.relabel j) (suffix.relabel j) (index.relabel j)
     (value.relabel j) suffixIndex suffixCount)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply InternalFiniteBlocksProof.elimination body alpha 2 Delta (tailMatrix frontCount suffix index value) psi h
 apply next (alpha ⊕ Fin 2) Sum.inl
   (tailMatrix frontCount suffix index value :: Delta.map (fun f => f.relabel Sum.inl))
   (.var (.inr 0)) (.var (.inr 1))
 · intro f hf
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupBindingProof
