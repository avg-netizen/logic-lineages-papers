module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnSubst emb bindEmbedding liftBind varBind sucSubst zSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalListInduction (atCode atIndex)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparsePositiveHeadDecompositionHeadSyntaxProof (graph4Subst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFilterCompletenessSyntaxProof (scanSubst)

abbrev test (E : Program 4) {α : Type} (ctx ty w k : OTerm α) : Formula α :=
  eqn w k ⊔ acceptEdge E ctx ty w k

private theorem orSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

private theorem testSubst (E : Program 4) {α β : Type} (ctx ty w k : OTerm α) (ts : α → OTerm β) :
    (test E ctx ty w k).subst (fun a => emb (ts a)) = test E (ctx.subst ts) (ty.subst ts) (w.subst ts) (k.subst ts) := by
  simp only [test,orSubst,eqnSubst,acceptEdge,edgeTape,graph4Subst,sucSubst,zSubst]

def fromRow (E : Program 4) {α : Type} (code ctx ty w k : OTerm α) : Formula α :=
  (witnessRow E code ctx ty w k).imp (scanGraph E code ctx ty k)

private theorem fromRowSubst (E : Program 4) {α β : Type} (code ctx ty w k : OTerm α) (ts : α → OTerm β) :
    (fromRow E code ctx ty w k).subst (fun a => emb (ts a)) =
      fromRow E (code.subst ts) (ctx.subst ts) (ty.subst ts) (w.subst ts) (k.subst ts) := by
  simp only [fromRow,witnessRow,impSubst,conjunctionSubst,memberSubst,orSubst,eqnSubst,
    acceptEdge,edgeTape,graph4Subst,scanSubst,sucSubst,zSubst]

theorem fromRowRename (E : Program 4) {α β : Type} (code ctx ty w k : OTerm α) (j : α → β) :
    (fromRow E code ctx ty w k).relabel j =
      fromRow E (code.relabel j) (ctx.relabel j) (ty.relabel j) (w.relabel j) (k.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fromRow E code ctx ty w k).subst (fun a => emb (.var (j a))) = _
  rw [fromRowSubst]
  simp only [termRelabelAsSubst]

abbrev motive (E : Program 4) {α : Type} (ctx ty w k : OTerm α) : Formula (α ⊕ Fin 1) :=
  fromRow E (.var (.inr 0)) (ctx.relabel Sum.inl) (ty.relabel Sum.inl) (w.relabel Sum.inl) (k.relabel Sum.inl)

theorem motiveAt (E : Program 4) {α : Type} (code ctx ty w k : OTerm α) :
    atCode (motive E ctx ty w k) code = fromRow E code ctx ty w k := by
  simp only [atCode,motive,instantiate,bindEmbedding,fromRowSubst,liftBind,varBind]

theorem motiveIndex (E : Program 4) {α : Type} (ctx ty w k : OTerm α) (i : Fin 3) :
    atIndex (motive E ctx ty w k) i = fromRow E (.var (.inr i)) (ctx.relabel Sum.inl)
      (ty.relabel Sum.inl) (w.relabel Sum.inl) (k.relabel Sum.inl) := by
  unfold atIndex motive
  rw [fromRowRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

theorem moveTest {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (E : Program 4)
    (ctx ty w h k : OTerm α) (same : Derivation body Γ (eqn w h)) (theTest : Derivation body Γ (test E ctx ty w k)) :
    Nonempty (Derivation body Γ (test E ctx ty h k)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let θ := test E (ctx.relabel j) (ty.relabel j) (.var (.inr 0)) (k.relabel j)
  have inst (x : OTerm α) : instantiate θ (emb x) = test E ctx ty x k := by
    simp only [θ,j,instantiate,bindEmbedding,testSubst,liftBind,varBind]
  have out := Derivation.equalityElimination θ (emb w) (emb h) same (by rw [inst]; exact theTest)
  rw [inst] at out
  exact ⟨out⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessSyntaxProof
