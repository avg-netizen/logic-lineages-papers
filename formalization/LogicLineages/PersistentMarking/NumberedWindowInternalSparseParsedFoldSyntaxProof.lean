module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseParserPositiveCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalStrongInduction
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb suc bindEmbedding liftBind varBind sucSubst)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalTermSubstitutionSyntaxProof (formulaSubstComposition onTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open NumberedWindowTypeFormulaSubstitutionProof (impSubst)
open NumberedWindowInternalSparseFieldParser (parser)

/-- The two distinguished slots are, in order, the original raw code and
its actual scratch output. All remaining terms are source parameters. -/
def pairAt {α β : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n s : OTerm β) : Formula β :=
  theta.subst (fun i => emb (Sum.elim r ![n,s] i))

def positiveGraph {α : Type} (n s : OTerm α) : Formula α :=
  programGraph parser (suc s) ![n]

def parsedMatrix {α β : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n : OTerm β) : Formula (β ⊕ Fin 1) :=
  (positiveGraph (n.relabel Sum.inl) (.var (.inr (0 : Fin 1)))).imp
    (pairAt theta (fun i => (r i).relabel Sum.inl) (n.relabel Sum.inl) (.var (.inr (0 : Fin 1))))

/-- The scratch code is quantified only after the original raw index has
been chosen. A malformed raw code has no successful hypothesis. -/
def parsedAt {α β : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n : OTerm β) : Formula β :=
  allOne (parsedMatrix theta r n)

def foldMotive {α : Type} (theta : Formula (α ⊕ Fin 2)) : Formula (α ⊕ Fin 1) :=
  parsedAt theta (fun i => .var (.inl i)) (.var (.inr (0 : Fin 1)))

theorem pairAtSubst {α β γ : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n s : OTerm β) (ts : β → OTerm γ) :
    (pairAt theta r n s).subst (fun i => emb (ts i)) =
      pairAt theta (fun i => (r i).subst ts) (n.subst ts) (s.subst ts) := by
  unfold pairAt
  rw [formulaSubstComposition]
  congr 1
  funext i
  cases i with
  | inl a => exact (onTermSubst arithmeticEmbedding (r a) ts).symm
  | inr i =>
    exact Fin.cases (onTermSubst arithmeticEmbedding n ts).symm
      (Fin.cases (onTermSubst arithmeticEmbedding s ts).symm (fun k => Fin.elim0 k)) i

theorem pairAtRename {α β γ : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n s : OTerm β) (j : β → γ) :
    (pairAt theta r n s).relabel j =
      pairAt theta (fun i => (r i).relabel j) (n.relabel j) (s.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (pairAt theta r n s).subst (fun i => emb (.var (j i))) = _
  simp only [pairAtSubst,← termRelabelAsSubst]

theorem positiveGraphSubst {α β : Type} (n s : OTerm α) (ts : α → OTerm β) :
    (positiveGraph n s).subst (fun i => emb (ts i)) = positiveGraph (n.subst ts) (s.subst ts) := by
  unfold positiveGraph
  rw [programSubst,sucSubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem parsedAtSubst {α β γ : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n : OTerm β) (ts : β → OTerm γ) :
    (parsedAt theta r n).subst (fun i => emb (ts i)) =
      parsedAt theta (fun i => (r i).subst ts) (n.subst ts) := by
  simp only [parsedAt,parsedMatrix,allEmbeddedSubst,impSubst,positiveGraphSubst,pairAtSubst,
    liftTermSubst] <;> rfl

theorem parsedAtRename {α β γ : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n : OTerm β) (j : β → γ) :
    (parsedAt theta r n).relabel j =
      parsedAt theta (fun i => (r i).relabel j) (n.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (parsedAt theta r n).subst (fun i => emb (.var (j i))) = _
  simp only [parsedAtSubst,← termRelabelAsSubst]

theorem parsedMatrixAt {α β : Type} (theta : Formula (α ⊕ Fin 2)) (r : α → OTerm β)
    (n s : OTerm β) :
    instantiate (parsedMatrix theta r n) (emb s) =
      (positiveGraph n s).imp (pairAt theta r n s) := by
  simp only [parsedMatrix,instantiate,bindEmbedding,impSubst,positiveGraphSubst,pairAtSubst,
    liftBind,varBind]

theorem foldMotiveAt {α : Type} (theta : Formula (α ⊕ Fin 2)) (n : OTerm α) :
    instantiate (foldMotive theta) (emb n) = parsedAt theta Term.var n := by
  rw [foldMotive,instantiate,bindEmbedding,parsedAtSubst] <;> rfl

theorem relocatedFoldMotiveAt {α β : Type} (theta : Formula (α ⊕ Fin 2))
    (j : (α ⊕ Fin 1) → β) (n : OTerm β) :
    instantiate ((lift (foldMotive theta)).relabel (Sum.map j id)) (emb n) =
      parsedAt theta (fun a => .var (j (.inl a))) n := by
  rw [lift,foldMotive,parsedAtRename,parsedAtRename,instantiate,bindEmbedding,parsedAtSubst] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseParsedFoldSyntaxProof
