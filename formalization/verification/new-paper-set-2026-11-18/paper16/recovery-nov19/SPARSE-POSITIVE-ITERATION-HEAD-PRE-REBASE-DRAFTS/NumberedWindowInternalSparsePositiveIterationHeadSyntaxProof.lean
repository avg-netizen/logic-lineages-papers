module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnSubst sucSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof
  (allBlockSubst liftedEmbedding conjunctionSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalTermSubstitutionProof
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparsePositiveFoldTargets (loopGraph)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopSubst)

/-- Exactly one original context/type and two seed coordinate pairs. -/
structure Plan (α : Type) where
  context : OTerm α
  ty : OTerm α
  originalCurrent : OTerm α
  originalCertificate : OTerm α
  nextCurrent : OTerm α
  nextCertificate : OTerm α

def Plan.map {α β : Type} (p : Plan α) (f : OTerm α → OTerm β) : Plan β :=
  ⟨f p.context,f p.ty,f p.originalCurrent,f p.originalCertificate,f p.nextCurrent,f p.nextCertificate⟩

abbrev oldLoop {α : Type} (raw : Program 5) (least : Program 3) (p : Plan α)
    (out fuel : OTerm α) :=
  loopGraph raw least out fuel p.context p.ty p.originalCurrent p.originalCertificate

abbrev newLoop {α : Type} (raw : Program 5) (least : Program 3) (p : Plan α)
    (out fuel : OTerm α) :=
  loopGraph raw least out fuel p.context p.ty p.nextCurrent p.nextCertificate

def headMatrix {α : Type} (raw : Program 5) (least : Program 3)
    (fuel : OTerm α) (p : Plan α) : Formula (α ⊕ Fin 2) :=
  let lift := fun t : OTerm α => t.relabel (Sum.inl : α → α ⊕ Fin 2)
  let p' := p.map lift
  let l : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let r : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  (oldLoop raw least p' l (suc (lift fuel)) ⊓ newLoop raw least p' r (lift fuel)).imp (eqn l r)

def sameAt {α : Type} (raw : Program 5) (least : Program 3) (fuel : OTerm α) (p : Plan α) : Formula α :=
  allBlock (headMatrix raw least fuel p)

theorem sameAtSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (fuel : OTerm α) (p : Plan α) (ts : α → OTerm β) :
    (sameAt raw least fuel p).subst (fun a => emb (ts a)) =
      sameAt raw least (fuel.subst ts) (p.map (fun t => t.subst ts)) := by
  unfold sameAt headMatrix
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [oldLoop,newLoop,loopSubst,eqnSubst,Plan.map,liftSubst,sucSubst,Term.subst,Sum.elim_inr]

theorem sameAtRename {α β : Type} (raw : Program 5) (least : Program 3)
    (fuel : OTerm α) (p : Plan α) (j : α → β) :
    (sameAt raw least fuel p).relabel j =
      sameAt raw least (fuel.relabel j) (p.map (fun t => t.relabel j)) := by
  rw [formulaRelabelAsSubst]
  change (sameAt raw least fuel p).subst (fun a => emb (.var (j a))) = _
  rw [sameAtSubst]
  simp only [← termRelabelAsSubst]

theorem headWitness {α : Type} (raw : Program 5) (least : Program 3)
    (fuel : OTerm α) (p : Plan α) (l r : OTerm α) :
    (headMatrix raw least fuel p).subst (Sum.elim Term.var (fun i => emb (![l,r] i))) =
      (oldLoop raw least p l (suc fuel) ⊓ newLoop raw least p r fuel).imp (eqn l r) := by
  have h : (Sum.elim Term.var (fun i : Fin 2 => emb (![l,r] i))) =
      (fun a => emb (Sum.elim Term.var ![l,r] a)) := by
    funext a
    cases a <;> rfl
  unfold headMatrix
  rw [h,impSubst,conjunctionSubst]
  simp only [oldLoop,newLoop,loopSubst,eqnSubst,Plan.map,sucSubst,witnessLift,Term.subst,Sum.elim_inr] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationHeadSyntaxProof
