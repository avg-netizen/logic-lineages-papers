module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn eqnRelabel eqnSubst bindEmbedding liftBind varBind zRelabel sucRelabel zSubst sucSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseDirectedSeen

attribute [local irreducible] programGraph

private theorem orRename {α β : Type} (p q : Formula α) (j : α → β) :
    (p ⊔ q).relabel j = p.relabel j ⊔ q.relabel j := rfl

private theorem orSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

private theorem graph4Rename {α β : Type} (p : Program 4) (o a b c d : OTerm α) (j : α → β) :
    (programGraph p o ![a,b,c,d]).relabel j =
      programGraph p (o.relabel j) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j] := by
  rw [programRename,quadInputsRename]

private theorem graph4Subst {α β : Type} (p : Program 4) (o a b c d : OTerm α) (ts : α → OTerm β) :
    (programGraph p o ![a,b,c,d]).subst (fun x => emb (ts x)) =
      programGraph p (o.subst ts) ![a.subst ts,b.subst ts,c.subst ts,d.subst ts] := by
  have tape : (fun i => ((![a,b,c,d] : Fin 4 → OTerm α) i).subst ts) =
      ![a.subst ts,b.subst ts,c.subst ts,d.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun w =>
      Fin.cases ?_ (fun k => Fin.elim0 k) w) y) x) i <;> rfl
  rw [programSubst,tape]

private theorem memberSubst {α β : Type} (code w : OTerm α) (ts : α → OTerm β) :
    (memberGraph code w).subst (fun a => emb (ts a)) =
      memberGraph (code.subst ts) (w.subst ts) := by
  have tape : (fun i => ((![code,w] : Fin 2 → OTerm α) i).subst ts) =
      ![code.subst ts,w.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · obtain rfl := Fin.eq_zero j
      rfl
  unfold memberGraph
  rw [programSubst,tape,sucSubst,zSubst]

theorem scanRename {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (j : α → β) :
    (scanGraph E code ctx ty v).relabel j =
      scanGraph E (code.relabel j) (ctx.relabel j) (ty.relabel j) (v.relabel j) := by
  simp only [scanGraph,scanTape,graph4Rename,sucRelabel,zRelabel]

private theorem scanSubst {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (ts : α → OTerm β) :
    (scanGraph E code ctx ty v).subst (fun a => emb (ts a)) =
      scanGraph E (code.subst ts) (ctx.subst ts) (ty.subst ts) (v.subst ts) := by
  simp only [scanGraph,scanTape,graph4Subst,sucSubst,zSubst]

abbrev witnessBinder (E : Program 4) {α : Type} (code ctx ty v : OTerm α) : Formula (α ⊕ Fin 1) :=
  witnessRow E (code.relabel Sum.inl) (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    (.var (.inr 0)) (v.relabel Sum.inl)

theorem witnessUnfold (E : Program 4) {α : Type} (code ctx ty v : OTerm α) :
    seenWitness E code ctx ty v = existsOne (witnessBinder E code ctx ty v) := rfl

private theorem rowRename {α β : Type} (E : Program 4) (code ctx ty w v : OTerm α) (j : α → β) :
    (witnessRow E code ctx ty w v).relabel j =
      witnessRow E (code.relabel j) (ctx.relabel j) (ty.relabel j) (w.relabel j) (v.relabel j) := by
  simp only [witnessRow,conjunctionRename,orRename,graphRename,eqnRelabel,
    acceptEdge,edgeTape,graph4Rename,sucRelabel,zRelabel]

private theorem rowSubst {α β : Type} (E : Program 4) (code ctx ty w v : OTerm α) (ts : α → OTerm β) :
    (witnessRow E code ctx ty w v).subst (fun a => emb (ts a)) =
      witnessRow E (code.subst ts) (ctx.subst ts) (ty.subst ts) (w.subst ts) (v.subst ts) := by
  simp only [witnessRow,conjunctionSubst,orSubst,memberSubst,eqnSubst,
    acceptEdge,edgeTape,graph4Subst,sucSubst,zSubst]

theorem witnessInstance {α : Type} (E : Program 4) (code ctx ty w v : OTerm α) :
    instantiate (witnessBinder E code ctx ty v) (emb w) = witnessRow E code ctx ty w v := by
  simp only [instantiate,witnessBinder,bindEmbedding,rowSubst,liftBind,varBind]

theorem witnessRename {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (j : α → β) :
    (seenWitness E code ctx ty v).relabel j =
      seenWitness E (code.relabel j) (ctx.relabel j) (ty.relabel j) (v.relabel j) := by
  rw [witnessUnfold,witnessUnfold,existsRename]
  unfold witnessBinder
  rw [rowRename]
  simp only [Term.relabel_relabel] <;> rfl

private theorem witnessSubst {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (ts : α → OTerm β) :
    (seenWitness E code ctx ty v).subst (fun a => emb (ts a)) =
      seenWitness E (code.subst ts) (ctx.subst ts) (ty.subst ts) (v.subst ts) := by
  unfold seenWitness
  rw [existsSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

abbrev scanImplies {α : Type} (E : Program 4) (code ctx ty v : OTerm α) : Formula α :=
  (scanGraph E code ctx ty v).imp (seenWitness E code ctx ty v)

theorem impliesRename {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (j : α → β) :
    (scanImplies E code ctx ty v).relabel j =
      scanImplies E (code.relabel j) (ctx.relabel j) (ty.relabel j) (v.relabel j) := by
  change ((scanGraph E code ctx ty v).relabel j).imp ((seenWitness E code ctx ty v).relabel j) = _
  rw [scanRename,witnessRename]

private theorem impliesSubst {α β : Type} (E : Program 4) (code ctx ty v : OTerm α) (ts : α → OTerm β) :
    (scanImplies E code ctx ty v).subst (fun a => emb (ts a)) =
      scanImplies E (code.subst ts) (ctx.subst ts) (ty.subst ts) (v.subst ts) := by
  simp only [scanImplies,impSubst,scanSubst,witnessSubst]

/-- Only the actual ordered seen code varies under the original list induction. -/
abbrev invariant {α : Type} (E : Program 4) (ctx ty v : OTerm α) : Formula (α ⊕ Fin 1) :=
  scanImplies E (.var (.inr 0)) (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (v.relabel Sum.inl)

theorem invariantCode {α : Type} (E : Program 4) (ctx ty v code : OTerm α) :
    atCode (invariant E ctx ty v) code = scanImplies E code ctx ty v := by
  rw [atCode,instantiate,bindEmbedding]
  change (scanImplies E (.var (.inr 0)) (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    (v.relabel Sum.inl)).subst _ = _
  rw [impliesSubst]
  simp only [liftBind,varBind]

theorem invariantIndex {α : Type} (E : Program 4) (ctx ty v : OTerm α) (i : Fin 3) :
    atIndex (invariant E ctx ty v) i =
      scanImplies E (.var (.inr i)) (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (v.relabel Sum.inl) := by
  unfold atIndex
  change (scanImplies E (.var (.inr 0)) (ctx.relabel Sum.inl) (ty.relabel Sum.inl)
    (v.relabel Sum.inl)).relabel _ = _
  rw [impliesRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
