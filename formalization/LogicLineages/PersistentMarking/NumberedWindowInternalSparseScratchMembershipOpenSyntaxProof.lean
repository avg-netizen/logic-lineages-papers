module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding varBind liftBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipTargets

attribute [local irreducible] programGraph

theorem graphRename {α β : Type} (code k : OTerm α) (j : α → β) :
    (memberGraph code k).relabel j = memberGraph (code.relabel j) (k.relabel j) := by
  unfold memberGraph
  rw [programRename,binaryInputsRename,sucRelabel,zRelabel]

private theorem graphSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) = memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

private theorem occursRename {α β : Type} (code k : OTerm α) (j : α → β) :
    (selectedOccurs code k).relabel j = selectedOccurs (code.relabel j) (k.relabel j) := by
  change ((unary scratchMinimum (suc k) code).relabel j).imp ((memberGraph code k).relabel j) = _
  rw [unaryRename,graphRename,sucRelabel] <;> rfl

private theorem occursSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (selectedOccurs code k).subst (fun a => emb (ts a)) =
      selectedOccurs (code.subst ts) (k.subst ts) := by
  simp only [selectedOccurs,impSubst,unarySubst,graphSubst,sucSubst]

/-- Fixed arithmetic candidate; only the real scratch code is generalized. -/
abbrev invariant {α : Type} (k : OTerm α) : Formula (α ⊕ Fin 1) :=
  selectedOccurs (.var (.inr 0)) (k.relabel Sum.inl)

theorem invariantCode {α : Type} (k n : OTerm α) :
    atCode (invariant k) n = selectedOccurs n k := by
  rw [atCode,instantiate,bindEmbedding]
  change (selectedOccurs (.var (.inr 0)) (k.relabel Sum.inl)).subst _ = _
  rw [occursSubst]
  simp only [liftBind,varBind]

theorem invariantIndex {α : Type} (k : OTerm α) (i : Fin 3) :
    atIndex (invariant k) i = selectedOccurs (.var (.inr i)) (k.relabel Sum.inl) := by
  unfold atIndex
  change (selectedOccurs (.var (.inr 0)) (k.relabel Sum.inl)).relabel _ = _
  rw [occursRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
