module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExcessTerminalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalListInductionSyntaxProof (allBlockRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst witnessLift)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalStrongInductionSyntaxProof (belowRename)
open ID1Completion.InternalAdditionLawsProof (add addSubst impSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (addRelabel)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb bindEmbedding bindTerm varBind zSubst sucSubst sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (frameValueTerm)
open NumberedWindowInternalSparseRawRun (ownRun)
open NumberedWindowInternalSparseRawRunLiftOwnProof (initialTerm)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (stateSubst stateRename rawConsSubst)
open NumberedWindowInternalLiteralExcessTerminalProof (LitRun TerminalOne runRename)

def Row {α : Type} (p other : Program 3) (q w r k : OTerm α) : Formula α :=
  (LitRun p other TerminalOne (add w k) q w r).imp (programGraph (ownRun p other) (suc z) ![q,w,r])

def Matrix {α : Type} (p other : Program 3) (w : OTerm α) : Formula (α ⊕ Fin 3) :=
  Row p other (.var (.inr 0)) (w.relabel Sum.inl) (.var (.inr 1)) (.var (.inr 2))

def Measure {α : Type} (p other : Program 3) (w : OTerm α) : Formula α :=
  allBlock (Matrix p other w)

def Predicate {α : Type} (p other : Program 3) : Formula (α ⊕ Fin 1) :=
  Measure p other (.var (.inr 0))

def Smaller {α : Type} (p other : Program 3) (w : OTerm α) : Formula α :=
  below (Predicate p other) w

private theorem starterSubst {α β : Type} (q w r : OTerm α) (ts : α → OTerm β) :
    (initialTerm (![q,w,r] : Fin 3 → OTerm α)).subst ts =
      initialTerm (![q.subst ts,w.subst ts,r.subst ts] : Fin 3 → OTerm β) := by
  simp only [initialTerm,stateSubst,frameValueTerm,sucSubst,rawConsSubst,zSubst]
  rfl

theorem rowSubst {α β : Type} (p other : Program 3) (q w r k : OTerm α) (ts : α → OTerm β) :
    (Row p other q w r k).subst (fun a => emb (ts a)) =
      Row p other (q.subst ts) (w.subst ts) (r.subst ts) (k.subst ts) := by
  have pairEq : (fun i : Fin 2 =>
      ((![add w k,initialTerm (![q,w,r])] : Fin 2 → OTerm α) i).subst ts) =
      ![add (w.subst ts) (k.subst ts),initialTerm (![q.subst ts,w.subst ts,r.subst ts])] := by
    funext i
    exact Fin.cases (addSubst w k ts) (Fin.cases (starterSubst q w r ts) (fun k => Fin.elim0 k)) i
  have tripleEq : (fun i : Fin 3 => ((![q,w,r] : Fin 3 → OTerm α) i).subst ts) =
      ![q.subst ts,w.subst ts,r.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [Row,impSubst,LitRun,programSubst,stateSubst,sucSubst,zSubst,pairEq,tripleEq]

theorem rowRename {α β : Type} (p other : Program 3) (q w r k : OTerm α) (j : α → β) :
    (Row p other q w r k).relabel j =
      Row p other (q.relabel j) (w.relabel j) (r.relabel j) (k.relabel j) := by
  change ((LitRun p other TerminalOne (add w k) q w r).relabel j).imp
    ((programGraph (ownRun p other) (suc z) ![q,w,r]).relabel j) = _
  rw [runRename]
  simp only [stateRename,sucRelabel,zRelabel,programRename,tripleInputsRename,addRelabel,Row]

theorem measureSubst {α β : Type} (p other : Program 3) (w : OTerm α) (ts : α → OTerm β) :
    (Measure p other w).subst (fun a => emb (ts a)) = Measure p other (w.subst ts) := by
  unfold Measure Matrix
  rw [allBlockSubst,liftedEmbedding,rowSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem measureRename {α β : Type} (p other : Program 3) (w : OTerm α) (j : α → β) :
    (Measure p other w).relabel j = Measure p other (w.relabel j) := by
  unfold Measure Matrix
  rw [allBlockRename,rowRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

theorem matrixWitness {α : Type} (p other : Program 3) (q w r k : OTerm α) :
    (Matrix p other w).subst (Sum.elim Term.var (fun i => emb (![q,r,k] i))) = Row p other q w r k := by
  have he : (Sum.elim Term.var (fun i => emb (![q,r,k] i))) =
      (fun a => emb (Sum.elim Term.var ![q,r,k] a)) := by
    funext a
    cases a <;> rfl
  unfold Matrix
  rw [he,rowSubst]
  simp only [witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem predicateInstantiate {α : Type} (p other : Program 3) (w : OTerm α) :
    instantiate (Predicate p other) (emb w) = Measure p other w := by
  rw [Predicate,instantiate,bindEmbedding,measureSubst,varBind]

theorem predicateLift {α : Type} (p other : Program 3) :
    lift (Predicate p other (α := α)) = Predicate p other (α := α ⊕ Fin 1) := by
  unfold lift Predicate
  rw [measureRename]
  rfl

theorem smallerRename {α β : Type} (p other : Program 3) (w : OTerm α) (j : α → β) :
    (Smaller p other w).relabel j = Smaller p other (w.relabel j) := by
  unfold Smaller Predicate
  rw [belowRename,measureRename]
  rfl

#print axioms rowSubst
#print axioms matrixWitness
#print axioms predicateLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFuelMotiveSyntaxProof
