module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn z suc sucSubst zSubst sucRelabel zRelabel bindTerm bindEmbedding liftBind varBind)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (numeralSubst)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding conjunctionSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename roundSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalLiteralPackedLeastOnProof (leastOnGraph)
open NumberedWindowInternalLiteralLeastOnMembersProof (leastOnRename)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof

attribute [local irreducible] programGraph

theorem appAuxSubst {α β : Type} (d e l r : OTerm α) (ts : α → OTerm β) :
    (auxiliaryTerm d e l r).subst ts =
      auxiliaryTerm (d.subst ts) (e.subst ts) (l.subst ts) (r.subst ts) := by
  simp only [auxiliaryTerm,rawConsSubst,numeralSubst,zSubst]

theorem appAuxRename {α β : Type} (d e l r : OTerm α) (j : α → β) :
    (auxiliaryTerm d e l r).relabel j =
      auxiliaryTerm (d.relabel j) (e.relabel j) (l.relabel j) (r.relabel j) := by
  simp only [auxiliaryTerm,rawConsRename,numeralRename,zRelabel]

theorem appLeastSubst {α β : Type} (C : Program 3) (Q : Program 4) (s : Settings)
    (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastOnGraph C Q s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastOnGraph C Q s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) =
      ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastOnGraph,programSubst,sucSubst,tape]

section
variable (N : Program 1) (C : Program 3) (Q : Program 4) (varyArgument : Bool) (s : Settings)

theorem motiveRename {α β : Type} (ctx ty dom cod arg μ m k : OTerm α) (j : α → β) :
    (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k).relabel j =
      appMotive N C Q varyArgument s (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j)
        (arg.relabel j) (μ.relabel j) (m.relabel j) (k.relabel j) := by
  cases varyArgument <;> simp only [appMotive,conjunctionRename,unaryRename,leastOnRename,varyAuxiliary,
    Bool.false_eq_true,ite_false,ite_true,appAuxRename]

theorem motiveSubst {α β : Type} (ctx ty dom cod arg μ m k : OTerm α) (ts : α → OTerm β) :
    (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k).subst (fun a => emb (ts a)) =
      appMotive N C Q varyArgument s (ctx.subst ts) (ty.subst ts) (dom.subst ts) (cod.subst ts)
        (arg.subst ts) (μ.subst ts) (m.subst ts) (k.subst ts) := by
  cases varyArgument <;> simp only [appMotive,conjunctionSubst,unarySubst,appLeastSubst,varyAuxiliary,
    Bool.false_eq_true,ite_false,ite_true,appAuxSubst]

variable (E : Program 4)

/-- Only the pool and the member are bound; every other input is a fixed parameter. -/
def matrix {α : Type} (vertices fctx fty seed ctx ty dom cod arg μ m elapsed : OTerm α) :
    Formula (α ⊕ Fin 2) :=
  let l : OTerm α → OTerm (α ⊕ Fin 2) := fun t => t.relabel Sum.inl
  (roundGraph E (.var (.inr 0)) (l elapsed) (l vertices) (l fctx) (l fty) (l seed) ⊓
    memberGraph (.var (.inr 0)) (.var (.inr 1))).imp
    (appMotive N C Q varyArgument s (l ctx) (l ty) (l dom) (l cod) (l arg) (l μ) (l m) (.var (.inr 1)))

def AtCount {α : Type} (vertices fctx fty seed ctx ty dom cod arg μ m elapsed : OTerm α) : Formula α :=
  allBlock (matrix N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed)

theorem atCountSubst {α β : Type} (vertices fctx fty seed ctx ty dom cod arg μ m elapsed : OTerm α)
    (ts : α → OTerm β) :
    (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed).subst (fun a => emb (ts a)) =
      AtCount N C Q varyArgument s E (vertices.subst ts) (fctx.subst ts) (fty.subst ts) (seed.subst ts)
        (ctx.subst ts) (ty.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts) (μ.subst ts)
        (m.subst ts) (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,roundSubst,memberSubst,motiveSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem atCountRename {α β : Type} (vertices fctx fty seed ctx ty dom cod arg μ m elapsed : OTerm α)
    (j : α → β) :
    (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed).relabel j =
      AtCount N C Q varyArgument s E (vertices.relabel j) (fctx.relabel j) (fty.relabel j) (seed.relabel j)
        (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j)
        (m.relabel j) (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed).subst
    (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]

theorem matrixWitness {α : Type} (vertices fctx fty seed ctx ty dom cod arg μ m elapsed out k : OTerm α) :
    (matrix N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed).subst
      (Sum.elim Term.var (fun i => emb (![out,k] i))) =
      (roundGraph E out elapsed vertices fctx fty seed ⊓ memberGraph out k).imp
        (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k) := by
  have he : (Sum.elim Term.var (fun i => emb (![out,k] i))) =
      (fun a => emb (Sum.elim Term.var ![out,k] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,conjunctionSubst,roundSubst,memberSubst,motiveSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Δ : List (Formula α)}
    (vertices fctx fty seed ctx ty dom cod arg μ m elapsed out k : OTerm α)
    (row : Nonempty (Derivation body Δ (AtCount N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed)))
    (round : Nonempty (Derivation body Δ (roundGraph E out elapsed vertices fctx fty seed)))
    (member : Nonempty (Derivation body Δ (memberGraph out k))) :
    Nonempty (Derivation body Δ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
  obtain ⟨h⟩ := ID1Completion.InternalClosedProgramsBindingProof.elimination body α 2 Δ
    (matrix N C Q varyArgument s E vertices fctx fty seed ctx ty dom cod arg μ m elapsed)
    (fun i => emb (![out,k] i)) row
  rw [matrixWitness] at h
  obtain ⟨r⟩ := round
  obtain ⟨mm⟩ := member
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction r mm)⟩

/-- Transport of the motive along an object equality of members. -/
theorem moveMotive {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx ty dom cod arg μ m w k : OTerm α) (same : Derivation body Γ (eqn w k))
    (d : Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m w)) :
    Nonempty (Derivation body Γ (appMotive N C Q varyArgument s ctx ty dom cod arg μ m k)) := by
  let l : OTerm α → OTerm (α ⊕ Fin 1) := fun t => t.relabel Sum.inl
  let θ : Formula (α ⊕ Fin 1) :=
    appMotive N C Q varyArgument s (l ctx) (l ty) (l dom) (l cod) (l arg) (l μ) (l m) (.var (.inr 0))
  have inst (x : OTerm α) : instantiate θ (emb x) = appMotive N C Q varyArgument s ctx ty dom cod arg μ m x := by
    simp only [θ,l,instantiate,bindEmbedding,motiveSubst,liftBind,varBind]
  have moved := Derivation.equalityElimination θ (emb w) (emb k) same (by rw [inst]; exact d)
  rw [inst] at moved
  exact ⟨moved⟩

/-- The relative edge premise moves along a renaming of contexts. -/
theorem stepRename {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)}
    (fctx fty ctx ty dom cod arg μ m : OTerm α)
    (step : ApplicationEdgeStepAt E N C Q varyArgument s body Γ fctx fty ctx ty dom cod arg μ m)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ) :
    ApplicationEdgeStepAt E N C Q varyArgument s body Δ (fctx.relabel j) (fty.relabel j) (ctx.relabel j)
      (ty.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) (μ.relabel j) (m.relabel j) := by
  intro γ i Θ w k retain edge here
  have both (q : Formula α) (hq : q ∈ Γ) : q.relabel (i ∘ j) ∈ Θ := by
    rw [← ID1Completion.InternalPositiveUnfoldingSupportProof.formulaRelabelComposition j i q]
    exact retain (q.relabel j) (keep q hq)
  simp only [Term.relabel_relabel] at edge here ⊢
  exact step γ (i ∘ j) Θ w k both edge here

end

#print axioms applyAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoRoundApplicationSyntaxProof
