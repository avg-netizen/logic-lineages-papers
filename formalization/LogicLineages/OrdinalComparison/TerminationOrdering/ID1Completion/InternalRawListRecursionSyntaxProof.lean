module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalListCodec SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionSyntaxProof InternalRecursionGraphStepSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRecursionClosureSyntaxProof InternalClosedPrograms InternalBinderTransportProof
open InternalTermSubstitutionSyntaxProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof (impSubst)

theorem consTermSubst {L : Language} {α β : Type} {k : Nat} (t : L.Term α)
    (xs : Fin k → L.Term α) (ts : α → L.Term β) :
    (fun i => (Fin.cons (α := fun _ => L.Term α) t xs i).subst ts) =
      Fin.cons (α := fun _ => L.Term β) (t.subst ts) (fun i => (xs i).subst ts) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem emptySubst {L : Language} {α β : Type} (ts : α → L.Term β) :
    (fun i : Fin 0 => (Fin.elim0 i : L.Term α).subst ts) = Fin.elim0 := by
  funext i
  exact Fin.elim0 i

abbrev tableGraph {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (out code : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  programGraph (table base step) out (Fin.cons code params)

abbrev dropGraph {α : Type} (out index code : OTerm α) : Formula α :=
  programGraph drop out (Fin.cons index (Fin.cons code Fin.elim0))

abbrev lookupGraph {α : Type} (out index code : OTerm α) : Formula α :=
  programGraph lookup out (Fin.cons index (Fin.cons code Fin.elim0))

@[simp] theorem programSubst {k : Nat} {α β : Type} (p : Program k)
    (out : OTerm α) (xs : Fin k → OTerm α) (ts : α → OTerm β) :
    (programGraph p out xs).subst (fun a => emb (ts a)) =
      programGraph p (out.subst ts) (fun i => (xs i).subst ts) :=
  graphSubst _ _ _ _

@[simp] theorem recRename {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (out code : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (recGraph base step out code params).relabel j =
      recGraph base step (out.relabel j) (code.relabel j) (fun i => (params i).relabel j) := by
  simp only [recGraph,programRename,consTermRename]

@[simp] theorem tableRename {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (out code : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (tableGraph base step out code params).relabel j =
      tableGraph base step (out.relabel j) (code.relabel j) (fun i => (params i).relabel j) := by
  simp only [tableGraph,programRename,consTermRename]

@[simp] theorem dropRename {α β : Type} (out index code : OTerm α) (j : α → β) :
    (dropGraph out index code).relabel j = dropGraph (out.relabel j) (index.relabel j) (code.relabel j) := by
  simp only [dropGraph,programRename,consTermRename,emptyRename]

@[simp] theorem lookupRename {α β : Type} (out index code : OTerm α) (j : α → β) :
    (lookupGraph out index code).relabel j = lookupGraph (out.relabel j) (index.relabel j) (code.relabel j) := by
  simp only [lookupGraph,programRename,consTermRename,emptyRename]

def dropBody {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α) : Formula (α ⊕ Fin 3) :=
  (tableGraph base step (.var (.inr 1)) (.var (.inr 0)) (fun i => (params i).relabel Sum.inl) ⊓
    tableGraph base step (.var (.inr 2))
      (OrdinaryArithmetic.addTerm (.var (.inr 0)) (gap.relabel Sum.inl))
        (fun i => (params i).relabel Sum.inl)).imp
    (dropGraph (.var (.inr 1)) (gap.relabel Sum.inl) (.var (.inr 2)))

/-- Every older table is reached by exactly its index difference many tails. -/
def dropRow {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α) : Formula α :=
  allBlock (dropBody base step gap params)

theorem dropRowSubst {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (dropRow base step gap params).subst (fun a => emb (ts a)) =
      dropRow base step (gap.subst ts) (fun i => (params i).subst ts) := by
  unfold dropRow dropBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [tableGraph,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem dropRowRename {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (gap : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (dropRow base step gap params).relabel j =
      dropRow base step (gap.relabel j) (fun i => (params i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (dropRow base step gap params).subst (fun a => emb (.var (j a))) = _
  rw [dropRowSubst]
  simp only [← termRelabelAsSubst]

theorem dropBodyWitness {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (gap code small large : OTerm α) (params : Fin k → OTerm α) :
    (dropBody base step gap params).subst
      (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (tableGraph base step small code params ⊓
        tableGraph base step large (OrdinaryArithmetic.addTerm code gap) params).imp
          (dropGraph small gap large) := by
  have he : (Sum.elim Term.var (fun i => emb (![code,small,large] i))) =
      (fun a => emb (Sum.elim Term.var ![code,small,large] a)) := by
    funext a
    cases a <;> rfl
  unfold dropBody
  rw [he,impSubst,conjunctionSubst]
  simp only [tableGraph,dropGraph,programSubst,consTermSubst,InternalAdditionLawsProof.addSubst,
    witnessLift,Term.subst,Sum.elim_inr,emptySubst]
  rfl

theorem consStepSubst {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (out head tail : OTerm α) (params : Fin k → OTerm α) (ts : α → OTerm β) :
    (consStep base step out head tail params).subst (fun a => emb (ts a)) =
      consStep base step (out.subst ts) (head.subst ts) (tail.subst ts)
        (fun i => (params i).subst ts) := by
  unfold consStep
  rw [existsSubst,liftedEmbedding,conjunctionSubst]
  simp only [recGraph,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem consStepRename {k : Nat} {α β : Type} (base : Program k) (step : Program (k + 2))
    (out head tail : OTerm α) (params : Fin k → OTerm α) (j : α → β) :
    (consStep base step out head tail params).relabel j =
      consStep base step (out.relabel j) (head.relabel j) (tail.relabel j)
        (fun i => (params i).relabel j) := by
  rw [formulaRelabelAsSubst]
  change (consStep base step out head tail params).subst (fun a => emb (.var (j a))) = _
  rw [consStepSubst]
  simp only [← termRelabelAsSubst]

theorem consStepInstance {k : Nat} {α : Type} (base : Program k) (step : Program (k + 2))
    (out head tail result : OTerm α) (params : Fin k → OTerm α) :
    instantiate
      (recGraph base step (.var (.inr (0 : Fin 1))) (tail.relabel Sum.inl)
          (fun i => (params i).relabel Sum.inl) ⊓
        programGraph step (out.relabel Sum.inl)
          (Fin.cons (head.relabel Sum.inl) (Fin.cons (.var (.inr 0))
            (fun i => (params i).relabel Sum.inl)))) (emb result) =
      recGraph base step result tail params ⊓
        programGraph step out (Fin.cons head (Fin.cons result params)) := by
  rw [instantiate,bindEmbedding,conjunctionSubst]
  simp only [recGraph,programSubst,consTermSubst,liftBind,varBind]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
