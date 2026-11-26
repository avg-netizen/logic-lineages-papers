module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalListInduction (atCode atIndex)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst zSubst sucRelabel zRelabel bindEmbedding liftBind varBind)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalGraphCompositionSyntaxProof (exsSubst bindSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaExtensionSyntaxProof (impRename)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginKeptSplitTargets (piece evidence matrix splitExists)

attribute [local irreducible] programGraph

abbrev A (l r j : OTerm α) : Formula α := programGraph append j ![l,r]
abbrev C (l r : OTerm α) : Formula α := programGraph permutation (suc z) ![l,r]

def invariantBody (l r k s d j : OTerm α) : Formula α :=
  (A k d j ⊓ C s j).imp (splitExists l r k d)

def invariantMatrix (l r k s : OTerm α) : Formula (α ⊕ Fin 2) :=
  invariantBody (l.relabel Sum.inl) (r.relabel Sum.inl) (k.relabel Sum.inl) (s.relabel Sum.inl)
    (.var (.inr 0)) (.var (.inr 1))

def invariantAt (l r k s : OTerm α) : Formula α := allBlock (invariantMatrix l r k s)

def motive (l r s : OTerm α) : Formula (α ⊕ Fin 1) :=
  invariantAt (l.relabel Sum.inl) (r.relabel Sum.inl) (.var (.inr 0)) (s.relabel Sum.inl)

private theorem tapeSubst {β : Type} (x y : OTerm α) (σ : α → OTerm β) :
    (fun i : Fin 2 => ((![x,y] : Fin 2 → OTerm α) i).subst σ) =
      ![x.subst σ,y.subst σ] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i

private theorem pieceSubst {β : Type} (s l r j : OTerm α) (σ : α → OTerm β) :
    (piece s l r j).subst (fun i => emb (σ i)) =
      piece (s.subst σ) (l.subst σ) (r.subst σ) (j.subst σ) := by
  simp only [piece,conjunctionSubst,programSubst,tapeSubst,sucSubst,zSubst]

private theorem pieceRename {β : Type} (s l r j : OTerm α) (ρ : α → β) :
    (piece s l r j).relabel ρ =
      piece (s.relabel ρ) (l.relabel ρ) (r.relabel ρ) (j.relabel ρ) := by
  simp only [piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel]

private theorem existsBlockSubst {α β : Type} {k : Nat}
    (p : Formula (α ⊕ Fin k)) (σ : α → Term β) :
    (block p).subst σ =
      block (p.subst (Sum.elim (fun x => (σ x).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold block
  rw [exsSubst,bindSubst]

private theorem existsBlockRename {α β : Type} {k : Nat}
    (p : Formula (α ⊕ Fin k)) (ρ : α → β) :
    (block p).relabel ρ = block (p.relabel (Sum.map ρ id)) := by
  rw [formulaRelabelAsSubst,existsBlockSubst,formulaRelabelAsSubst]
  congr 2
  funext x
  cases x <;> rfl

theorem splitSubst {β : Type} (l r k d : OTerm α) (σ : α → OTerm β) :
    (splitExists l r k d).subst (fun i => emb (σ i)) =
      splitExists (l.subst σ) (r.subst σ) (k.subst σ) (d.subst σ) := by
  unfold splitExists
  rw [existsBlockSubst,liftedEmbedding]
  simp only [matrix,evidence,pieceSubst,conjunctionSubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem splitRename {β : Type} (l r k d : OTerm α) (ρ : α → β) :
    (splitExists l r k d).relabel ρ =
      splitExists (l.relabel ρ) (r.relabel ρ) (k.relabel ρ) (d.relabel ρ) := by
  unfold splitExists
  rw [existsBlockRename]
  have comp : ((Sum.map ρ id : α ⊕ Fin 8 → β ⊕ Fin 8) ∘ Sum.inl) = Sum.inl ∘ ρ := rfl
  simp only [matrix,evidence,pieceRename,conjunctionRename,Term.relabel_relabel,comp,Term.relabel] <;> rfl

private theorem rawBodySubst {β : Type} (l r k s d j : OTerm α) (σ : α → OTerm β) :
    (invariantBody l r k s d j).subst (fun i => emb (σ i)) =
      invariantBody (l.subst σ) (r.subst σ) (k.subst σ) (s.subst σ) (d.subst σ) (j.subst σ) := by
  simp only [invariantBody,A,C,impSubst,conjunctionSubst,programSubst,
    tapeSubst,sucSubst,zSubst,splitSubst]

private theorem rawBodyRename {β : Type} (l r k s d j : OTerm α) (ρ : α → β) :
    (invariantBody l r k s d j).relabel ρ =
      invariantBody (l.relabel ρ) (r.relabel ρ) (k.relabel ρ) (s.relabel ρ) (d.relabel ρ) (j.relabel ρ) := by
  simp only [invariantBody,A,C,impRename,conjunctionRename,programRename,
    binaryInputsRename,sucRelabel,zRelabel,splitRename]

theorem invariantWitness (l r k s d j : OTerm α) :
    (invariantMatrix l r k s).subst (Sum.elim Term.var (fun i => emb (![d,j] i))) =
      invariantBody l r k s d j := by
  let w : Fin 2 → OTerm α := ![d,j]
  have bridge : Sum.elim Term.var (fun i => emb (w i)) =
      (fun a => emb (Sum.elim Term.var w a)) := by
    funext a
    cases a <;> rfl
  change (invariantMatrix l r k s).subst (Sum.elim Term.var (fun i => emb (w i))) = _
  rw [bridge]
  simp only [invariantMatrix,rawBodySubst,witnessLift,Term.subst,Sum.elim_inr,w] <;> rfl

theorem invariantRename {β : Type} (l r k s : OTerm α) (ρ : α → β) :
    (invariantAt l r k s).relabel ρ =
      invariantAt (l.relabel ρ) (r.relabel ρ) (k.relabel ρ) (s.relabel ρ) := by
  unfold invariantAt
  rw [allBlockRename]
  have comp : ((Sum.map ρ id : α ⊕ Fin 2 → β ⊕ Fin 2) ∘ Sum.inl) = Sum.inl ∘ ρ := rfl
  simp only [invariantMatrix,rawBodyRename,Term.relabel_relabel,comp,Term.relabel] <;> rfl

private theorem invariantSubst {β : Type} (l r k s : OTerm α) (σ : α → OTerm β) :
    (invariantAt l r k s).subst (fun i => emb (σ i)) =
      invariantAt (l.subst σ) (r.subst σ) (k.subst σ) (s.subst σ) := by
  unfold invariantAt
  rw [allBlockSubst,liftedEmbedding]
  simp only [invariantMatrix,rawBodySubst,liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem motiveCode (l r k s : OTerm α) :
    atCode (motive l r s) k = invariantAt l r k s := by
  rw [atCode,instantiate,bindEmbedding]
  unfold motive
  rw [invariantSubst]
  simp only [liftBind,varBind]

theorem motiveIndex (l r s : OTerm α) (i : Fin 3) :
    atIndex (motive l r s) i =
      invariantAt (l.relabel Sum.inl) (r.relabel Sum.inl) (.var (.inr i)) (s.relabel Sum.inl) := by
  unfold atIndex motive
  rw [invariantRename]
  simp only [Term.relabel_relabel,Term.relabel] <;> rfl

#print axioms splitSubst
#print axioms invariantWitness
#print axioms motiveCode
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptInductionSyntaxProof
