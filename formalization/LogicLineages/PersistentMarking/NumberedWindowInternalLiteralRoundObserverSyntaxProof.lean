module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverInterfaceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucSubst)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (allBlockSubst liftedEmbedding conjunctionSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (witnessLift liftSubst)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalClosedPrograms (allBlock)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundSubst)
open NumberedWindowInternalLiteralRoundObserverTargets
attribute [local irreducible] programGraph

open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
variable (E : Program 4) (O : Program 3)
variable {α : Type}

theorem observeSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (observe O ctx ty seed x).subst (fun a => emb (ts a)) =
    observe O (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [observe,programSubst,tape]

theorem observeRename {β : Type} (ctx ty q m : OTerm α) (j : α → β) :
    (observe O ctx ty q m).relabel j = observe O (ctx.relabel j) (ty.relabel j) (q.relabel j) (m.relabel j) := by
  simp only [observe,InternalControlGraphSupportProof.programRename,
    NumberedWindowInternalSparseFieldParserOpenSyntaxProof.tripleInputsRename]

def matrix {alpha : Type} (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (inputs E O (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
    (observe O (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 5)) (.var (.inr 6)))

def AtCount {alpha : Type} (elapsed : OTerm alpha) : Formula alpha := allBlock (matrix E O elapsed)

theorem inputsSubst {alpha beta : Type} (elapsed vertices ctx ty seed out k m : OTerm alpha) (ts : alpha → OTerm beta) :
  (inputs E O elapsed vertices ctx ty seed out k m).subst (fun a => emb (ts a)) =
    inputs E O (elapsed.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (out.subst ts) (k.subst ts) (m.subst ts) := by
  simp only [inputs,conjunctionSubst,roundSubst,observeSubst,memberSubst]

theorem atCountSubst {alpha beta : Type} (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount E O elapsed).subst (fun a => emb (ts a)) = AtCount E O (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,inputsSubst,observeSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount E O elapsed).relabel j = AtCount E O (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount E O elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (elapsed vertices ctx ty seed out k m : OTerm alpha) :
    (matrix E O elapsed).subst (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (inputs E O elapsed vertices ctx ty seed out k m).imp
        (observe O ctx ty k m) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (fun a => emb (Sum.elim Term.var ![vertices,ctx,ty,seed,out,k,m] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,inputsSubst,observeSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (elapsed vertices ctx ty seed out k m : OTerm alpha)
    (row : Nonempty (Derivation body Delta (AtCount E O elapsed)))
    (data : Nonempty (Derivation body Delta (inputs E O elapsed vertices ctx ty seed out k m))) :
    Nonempty (Derivation body Delta (observe O ctx ty k m)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta (matrix E O elapsed)
    (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i)) row
  rw [matrixWitness] at h
  obtain ⟨d⟩ := data
  exact ⟨Derivation.implicationElimination h d⟩

#print axioms observeRename
#print axioms applyAt
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundObserverSyntaxProof
