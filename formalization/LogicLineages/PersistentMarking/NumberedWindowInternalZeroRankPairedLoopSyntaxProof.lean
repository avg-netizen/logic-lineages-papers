module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnSubst z zSubst suc sucSubst bindEmbedding)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding allBlockSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift)
open ID1Completion.InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalParameterizedPositiveFold (iterateAt)
open NumberedWindowInternalZeroRankStepTransportProof (zeroTail)
open NumberedWindowInternalZeroRankPairedStepProof (liveAgrees)

attribute [local irreducible] programGraph

def loop {α : Type} (A : Program 4) (out k c ty start raw : OTerm α) : Formula α :=
    programGraph (iterateAt A) out ![k,c,ty,start,raw]

private theorem vectorSub (α β : Type) (k c ty start raw : OTerm α) (ts : α → OTerm β) :
    (fun i : Fin 5 => (![k,c,ty,start,raw] i).subst ts) =
      ![k.subst ts,c.subst ts,ty.subst ts,start.subst ts,raw.subst ts] := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun d => Fin.cases ?_ (fun p => Fin.elim0 p) d) c) b) a) i <;> rfl

theorem loopSubst {α β : Type} (A : Program 4) (out k c ty start raw : OTerm α) (ts : α → OTerm β) :
    (loop A out k c ty start raw).subst (fun i => emb (ts i)) =
      loop A (out.subst ts) (k.subst ts) (c.subst ts) (ty.subst ts) (start.subst ts) (raw.subst ts) := by
  unfold loop
  rw [programSubst,vectorSub]

theorem loopRename {α β : Type} (A : Program 4) (out k c ty start raw : OTerm α) (j : α → β) :
    (loop A out k c ty start raw).relabel j =
      loop A (out.relabel j) (k.relabel j) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (loop A out k c ty start raw).subst (fun i => emb (.var (j i))) = _
  simp only [loopSubst,← termRelabelAsSubst]

private theorem zeroTailSubst {α β : Type} (out : OTerm α) (ts : α → OTerm β) :
    (zeroTail out).subst (fun i => emb (ts i)) = zeroTail (out.subst ts) := by
  unfold zeroTail unary
  rw [programSubst,zSubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

private theorem notSubst {α β : Type} (p : Formula α) (ts : α → Term β) :
    p.not.subst ts = (p.subst ts).not := rfl

theorem liveAgreesSubst {α β : Type} (out ordinary : OTerm α) (ts : α → OTerm β) :
    (liveAgrees out ordinary).subst (fun i => emb (ts i)) =
      liveAgrees (out.subst ts) (ordinary.subst ts) := by
  simp only [liveAgrees,impSubst,notSubst,zeroTailSubst,eqnSubst]

def matrix {α : Type} (A U : Program 4) (k c ty start raw out ordinary : OTerm α) : Formula α :=
  (loop A out k c ty start raw ⊓ loop U ordinary k c ty start raw).imp (liveAgrees out ordinary)

def rowsBody {α : Type} (A U : Program 4) (k c ty start raw : OTerm α) : Formula (α ⊕ Fin 2) :=
  matrix A U (k.relabel Sum.inl) (c.relabel Sum.inl) (ty.relabel Sum.inl) (start.relabel Sum.inl)
    (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))

def rows {α : Type} (A U : Program 4) (k c ty start raw : OTerm α) : Formula α :=
  allBlock (rowsBody A U k c ty start raw)

theorem matrixSubst {α β : Type} (A U : Program 4) (k c ty start raw out ord : OTerm α) (ts : α → OTerm β) :
    (matrix A U k c ty start raw out ord).subst (fun i => emb (ts i)) =
      matrix A U (k.subst ts) (c.subst ts) (ty.subst ts) (start.subst ts) (raw.subst ts)
        (out.subst ts) (ord.subst ts) := by
  simp only [matrix,impSubst,conjunctionSubst,loopSubst,liveAgreesSubst]

theorem rowsSubst {α β : Type} (A U : Program 4) (k c ty start raw : OTerm α) (ts : α → OTerm β) :
    (rows A U k c ty start raw).subst (fun i => emb (ts i)) =
      rows A U (k.subst ts) (c.subst ts) (ty.subst ts) (start.subst ts) (raw.subst ts) := by
  unfold rows rowsBody
  rw [allBlockSubst,liftedEmbedding,matrixSubst]
  simp only [ID1Completion.InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr] <;> rfl

theorem rowsRename {α β : Type} (A U : Program 4) (k c ty start raw : OTerm α) (j : α → β) :
    (rows A U k c ty start raw).relabel j =
      rows A U (k.relabel j) (c.relabel j) (ty.relabel j) (start.relabel j) (raw.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (rows A U k c ty start raw).subst (fun i => emb (.var (j i))) = _
  simp only [rowsSubst,← termRelabelAsSubst]

theorem rowsBodyWitness {α : Type} (A U : Program 4) (k c ty start raw out ord : OTerm α) :
    (rowsBody A U k c ty start raw).subst (Sum.elim Term.var (fun i => emb (![out,ord] i))) =
      matrix A U k c ty start raw out ord := by
  have e : (Sum.elim Term.var (fun i => emb (![out,ord] i))) =
      (fun i => emb (Sum.elim Term.var ![out,ord] i)) := by
    funext a
    cases a <;> rfl
  rw [rowsBody,e,matrixSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr] <;> rfl

#print axioms rowsBodyWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPairedLoopSyntaxProof
