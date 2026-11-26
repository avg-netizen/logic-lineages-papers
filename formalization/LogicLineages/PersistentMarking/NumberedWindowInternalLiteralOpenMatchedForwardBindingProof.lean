module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedForwardBindingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedSubst suppliedRename)

def pushed (L : Program 3) (raw : Program 5)
    {α : Type} (ctx cod parent earlier : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let later : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (reported L (ctx.relabel j) (cod.relabel j) (parent.relabel j) later ⊓
    supplied raw (L) (ctx.relabel j) (cod.relabel j) (earlier.relabel j) later)

theorem pushedRename {α β : Type} (L : Program 3)
    (raw : Program 5) (ctx cod parent earlier : OTerm α) (j : α → β) :
    (pushed L raw ctx cod parent earlier).relabel j =
      pushed L raw (ctx.relabel j) (cod.relabel j) (parent.relabel j) (earlier.relabel j) := by
  simp only [pushed,existsRename,conjunctionRename,reportedRename,suppliedRename,Term.relabel_relabel,Term.relabel]
  rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provideLater (L : Program 3) (raw : Program 5)
    (ctx cod parent earlier later : OTerm α)
    (found : Derivation B Γ (reported L ctx cod parent later))
    (path : Derivation B Γ (supplied raw (L) ctx cod earlier later)) :
    Nonempty (Derivation B Γ (pushed L raw ctx cod parent earlier)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := reported L (ctx.relabel j) (cod.relabel j) (parent.relabel j) x ⊓
    supplied raw (L) (ctx.relabel j) (cod.relabel j) (earlier.relabel j) x
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb later)
  simp only [clause,j,x,instantiate,bindEmbedding,conjunctionSubst,reportedSubst,suppliedSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction found path

#print axioms pushedRename
#print axioms provideLater
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedForwardBindingProof
