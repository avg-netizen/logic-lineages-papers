module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn sucRelabel zRelabel sucSubst zSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (graph3Subst graph3Rename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (windowTape)
open NumberedWindowInternalSparseDirectedFilter (passGraph passTape)
open NumberedWindowInternalSparsePassWindowTargets

attribute [local irreducible] programGraph

theorem windowRename {α β : Type} (W : Program 3) (ctx ty k : OTerm α) (j : α → β) :
    (windowAt W ctx ty k).relabel j = windowAt W (ctx.relabel j) (ty.relabel j) (k.relabel j) := by
  simp only [windowAt,windowTape,graph3Rename,sucRelabel,zRelabel]

theorem windowSubst {α β : Type} (W : Program 3) (ctx ty k : OTerm α) (ts : α → OTerm β) :
    (windowAt W ctx ty k).subst (fun a => emb (ts a)) = windowAt W (ctx.subst ts) (ty.subst ts) (k.subst ts) := by
  simp only [windowAt,windowTape,graph3Subst,sucSubst,zSubst]

theorem memberSubst {α β : Type} (code k : OTerm α) (ts : α → OTerm β) :
    (memberGraph code k).subst (fun a => emb (ts a)) = memberGraph (code.subst ts) (k.subst ts) := by
  have tape : (fun i => ((![code,k] : Fin 2 → OTerm α) i).subst ts) = ![code.subst ts,k.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem allSubst {α β : Type} (W : Program 3) (ctx ty code : OTerm α) (ts : α → OTerm β) :
    (allWindow W ctx ty code).subst (fun a => emb (ts a)) =
      allWindow W (ctx.subst ts) (ty.subst ts) (code.subst ts) := by
  simp only [allWindow,allEmbeddedSubst,impSubst,memberSubst,windowSubst,liftTermSubst]
  rfl

theorem allRename {α β : Type} (W : Program 3) (ctx ty code : OTerm α) (j : α → β) :
    (allWindow W ctx ty code).relabel j = allWindow W (ctx.relabel j) (ty.relabel j) (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (allWindow W ctx ty code).subst (fun a => emb (.var (j a))) = _
  rw [allSubst,← termRelabelAsSubst,← termRelabelAsSubst,← termRelabelAsSubst]

theorem passRename {α β : Type} (E : Program 4) (out vertices seen ctx ty : OTerm α) (j : α → β) :
    (passGraph E out vertices seen ctx ty).relabel j = passGraph E (out.relabel j)
      (vertices.relabel j) (seen.relabel j) (ctx.relabel j) (ty.relabel j) := by
  simp only [passGraph,passTape,programRename,quadInputsRename]

theorem specialize {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (W : Program 3)
    (ctx ty seen k : OTerm α) (d : Derivation body Γ (allWindow W ctx ty seen)) :
    Nonempty (Derivation body Γ ((memberGraph seen k).imp (windowAt W ctx ty k))) := by
  have guard := Derivation.universalElimination (emb k) d
  simpa only [instantiate,bindEmbedding,impSubst,memberSubst,windowSubst,liftBind,varBind] using
    (Nonempty.intro guard)

theorem moveGuard {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (W : Program 3)
    (ctx ty w k : OTerm α) (same : Derivation body Γ (eqn w k)) (d : Derivation body Γ (windowAt W ctx ty w)) :
    Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  let θ : Formula (α ⊕ Fin 1) := windowAt W (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (.var (.inr 0))
  have inst (x : OTerm α) : instantiate θ (emb x) = windowAt W ctx ty x := by
    simp only [θ,instantiate,bindEmbedding,windowSubst,liftBind,varBind]
  have moved := Derivation.equalityElimination θ (emb w) (emb k) same (by rw [inst]; exact d)
  rw [inst] at moved
  exact ⟨moved⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
