module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastTargets
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

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastSyntaxProof
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
open NumberedWindowInternalLiteralRoundLeastTargets
attribute [local irreducible] programGraph

open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
variable {α : Type}

theorem leastSubst {β : Type} (ctx ty seed x : OTerm α) (ts : α → OTerm β) :
    (leastGraph C X W s ctx ty seed x).subst (fun a => emb (ts a)) =
    leastGraph C X W s (ctx.subst ts) (ty.subst ts) (seed.subst ts) (x.subst ts) := by
  have tape : (fun i => ((![ctx,ty,seed] : Fin 3 → OTerm α) i).subst ts) = ![ctx.subst ts,ty.subst ts,seed.subst ts] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  simp only [leastGraph,programSubst,sucSubst,tape]

def matrix {alpha : Type} (elapsed : OTerm alpha) : Formula (alpha ⊕ Fin 7) :=
  (inputs C X W s (elapsed.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6))).imp
    (leastGraph C X W s (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 5)) (.var (.inr 6)))

def AtCount {alpha : Type} (elapsed : OTerm alpha) : Formula alpha := allBlock (matrix C X W s elapsed)

theorem inputsSubst {alpha beta : Type} (elapsed vertices ctx ty seed out k m : OTerm alpha) (ts : alpha → OTerm beta) :
  (inputs C X W s elapsed vertices ctx ty seed out k m).subst (fun a => emb (ts a)) =
    inputs C X W s (elapsed.subst ts) (vertices.subst ts) (ctx.subst ts) (ty.subst ts) (seed.subst ts) (out.subst ts) (k.subst ts) (m.subst ts) := by
  simp only [inputs,conjunctionSubst,roundSubst,leastSubst,memberSubst]

theorem atCountSubst {alpha beta : Type} (elapsed : OTerm alpha) (ts : alpha → OTerm beta) :
    (AtCount C X W s elapsed).subst (fun a => emb (ts a)) = AtCount C X W s (elapsed.subst ts) := by
  unfold AtCount matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,inputsSubst,leastSubst,liftSubst,Term.subst,Sum.elim_inr]
@[simp] theorem atCountRename {alpha beta : Type} (elapsed : OTerm alpha) (j : alpha → beta) :
    (AtCount C X W s elapsed).relabel j = AtCount C X W s (elapsed.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (AtCount C X W s elapsed).subst (fun a => emb (.var (j a))) = _
  rw [atCountSubst]
  simp only [← termRelabelAsSubst]
theorem matrixWitness {alpha : Type}
    (elapsed vertices ctx ty seed out k m : OTerm alpha) :
    (matrix C X W s elapsed).subst (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (inputs C X W s elapsed vertices ctx ty seed out k m).imp
        (leastGraph C X W s ctx ty k m) := by
  have he : (Sum.elim Term.var
      (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i))) =
      (fun a => emb (Sum.elim Term.var ![vertices,ctx,ty,seed,out,k,m] a)) := by
    funext a
    cases a <;> rfl
  unfold matrix
  rw [he]
  simp only [impSubst,inputsSubst,leastSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem applyAt {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (elapsed vertices ctx ty seed out k m : OTerm alpha)
    (row : Nonempty (Derivation body Delta (AtCount C X W s elapsed)))
    (data : Nonempty (Derivation body Delta (inputs C X W s elapsed vertices ctx ty seed out k m))) :
    Nonempty (Derivation body Delta (leastGraph C X W s ctx ty k m)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body alpha 7 Delta (matrix C X W s elapsed)
    (fun i => emb (![vertices,ctx,ty,seed,out,k,m] i)) row
  rw [matrixWitness] at h
  obtain ⟨d⟩ := data
  exact ⟨Derivation.implicationElimination h d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRoundLeastSyntaxProof
