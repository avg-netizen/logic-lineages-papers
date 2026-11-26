module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountSupportedSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel eqnSubst bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (add addSubst impSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalBinderTransportSyntaxProof (termRelabelSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalLiteralCountSupportedSyntaxProof (countedRename)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)

def query (front suffix key cr joined cl co : OTerm α) : Formula α :=
  (appended front suffix joined ⊓ (counted front key cl ⊓ counted joined key co)).imp
    (eqn co (add cl cr))

def matrix (front suffix key cr : OTerm α) : Formula (α ⊕ Fin 3) :=
  query (front.relabel Sum.inl) (suffix.relabel Sum.inl) (key.relabel Sum.inl) (cr.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))

def atFront (front suffix key cr : OTerm α) : Formula α := allBlock (matrix front suffix key cr)

def motive (suffix key cr : OTerm α) : Formula (α ⊕ Fin 1) :=
  atFront (.var (.inr 0)) (suffix.relabel Sum.inl) (key.relabel Sum.inl) (cr.relabel Sum.inl)

private theorem tapeSubst {α β : Type} (a b : OTerm α) (ts : α → OTerm β) :
    (fun i : Fin 2 => ((![a,b] : Fin 2 → OTerm α) i).subst ts) = ![a.subst ts,b.subst ts] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem countSubst {α β : Type} (a k n : OTerm α) (ts : α → OTerm β) :
    (counted a k n).subst (fun x => emb (ts x)) = counted (a.subst ts) (k.subst ts) (n.subst ts) := by
  simp only [counted,programSubst,tapeSubst]

private theorem appSubst {α β : Type} (a b u : OTerm α) (ts : α → OTerm β) :
    (appended a b u).subst (fun x => emb (ts x)) =
      appended (a.subst ts) (b.subst ts) (u.subst ts) := by
  simp only [appended,programSubst,tapeSubst]

theorem appRename {α β : Type} (a b u : OTerm α) (j : α → β) :
    (appended a b u).relabel j = appended (a.relabel j) (b.relabel j) (u.relabel j) := by
  simp only [appended,programRename,binaryInputsRename]

theorem queryRename {α β : Type} (a b k r u l o : OTerm α) (j : α → β) :
    (query a b k r u l o).relabel j =
      query (a.relabel j) (b.relabel j) (k.relabel j) (r.relabel j)
        (u.relabel j) (l.relabel j) (o.relabel j) := by
  simp only [query,impRename,conjunctionRename,appRename,countedRename,eqnRelabel,addRelabel]

private theorem querySubst {α β : Type} (a b k r u l o : OTerm α) (ts : α → OTerm β) :
    (query a b k r u l o).subst (fun i => emb (ts i)) =
      query (a.subst ts) (b.subst ts) (k.subst ts) (r.subst ts) (u.subst ts) (l.subst ts) (o.subst ts) := by
  simp only [query,impSubst,conjunctionSubst,appSubst,countSubst,eqnSubst,addSubst]

theorem matrixWitness {α : Type} (a b k r u l o : OTerm α) :
    (matrix a b k r).subst (Sum.elim Term.var (fun i => emb (![u,l,o] i))) =
      query a b k r u l o := by
  let ws : Fin 3 → OTerm α := ![u,l,o]
  have bridge : (Sum.elim Term.var (fun i => emb (ws i))) =
      (fun i => emb (Sum.elim Term.var ws i)) := by
    funext i
    cases i <;> rfl
  change (matrix a b k r).subst (Sum.elim Term.var (fun i => emb (ws i))) = _
  rw [bridge]
  simp only [matrix,querySubst,witnessLift,Term.subst,Sum.elim_inr,ws] <;> rfl

theorem atFrontRename {α β : Type} (a b k r : OTerm α) (j : α → β) :
    (atFront a b k r).relabel j = atFront (a.relabel j) (b.relabel j) (k.relabel j) (r.relabel j) := by
  unfold atFront
  rw [allBlockRename]
  have cp : ((Sum.map j id : α ⊕ Fin 3 → β ⊕ Fin 3) ∘ Sum.inl) = Sum.inl ∘ j := rfl
  simp only [matrix,queryRename,Term.relabel_relabel,cp,Term.relabel] <;> rfl

private theorem atFrontSubst {α β : Type} (a b k r : OTerm α) (ts : α → OTerm β) :
    (atFront a b k r).subst (fun i => emb (ts i)) =
      atFront (a.subst ts) (b.subst ts) (k.subst ts) (r.subst ts) := by
  unfold atFront
  rw [allBlockSubst,liftedEmbedding]
  simp only [matrix,querySubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem motiveCode {α : Type} (a b k r : OTerm α) :
    atCode (motive b k r) a = atFront a b k r := by
  rw [atCode,instantiate,bindEmbedding]
  unfold motive
  rw [atFrontSubst]
  simp only [liftBind,varBind]

theorem motiveIndex {α : Type} (b k r : OTerm α) (i : Fin 3) :
    atIndex (motive b k r) i =
      atFront (.var (.inr i)) (b.relabel Sum.inl) (k.relabel Sum.inl) (r.relabel Sum.inl) := by
  unfold atIndex motive
  rw [atFrontRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendSyntaxProof
