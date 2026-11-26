module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedReportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinApplicationHopBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralOpenMatchedReportProof
open NumberedWindowInternalLiteralOpenMatchedReportProof (pulled)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedSubst suppliedRename)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (K : MatchContext) (L : Program 3) (raw : Program 5)

theorem pulledRename {β : Type} (ctx cod parent value : OTerm α) (j : α → β) :
    (pulled L raw ctx cod parent value).relabel j =
    pulled L raw (ctx.relabel j) (cod.relabel j) (parent.relabel j) (value.relabel j) := by
  simp only [pulled,existsRename,conjunctionRename,reportedRename,suppliedRename,Term.relabel_relabel,Term.relabel]
  rfl

theorem provideEarlier (ctx cod parent value earlier : OTerm α)
    (found : Derivation body Γ (reported L ctx cod parent earlier))
    (path : Derivation body Γ (supplied raw (L) ctx cod earlier value)) :
    Nonempty (Derivation body Γ (pulled L raw ctx cod parent value)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := reported L (ctx.relabel j) (cod.relabel j) (parent.relabel j) x ⊓
    supplied raw (L) (ctx.relabel j) (cod.relabel j) x (value.relabel j)
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb earlier)
  simp only [clause,j,x,instantiate,bindEmbedding,conjunctionSubst,reportedSubst,suppliedSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction found path

theorem moveTarget (raw : Program 5) (least : Program 3) (ctx cod a r v : OTerm α)
    (same : Derivation body Γ (eqn r v)) (path : Derivation body Γ (supplied raw least ctx cod a r)) :
    Nonempty (Derivation body Γ (supplied raw least ctx cod a v)) := by
  let clause : Formula (α ⊕ Fin 1) := supplied raw least (ctx.relabel Sum.inl) (cod.relabel Sum.inl)
    (a.relabel Sum.inl) (.var (.inr 0))
  have inst (t : OTerm α) : instantiate clause (emb t) = supplied raw least ctx cod a t := by
    simp only [clause,instantiate,bindEmbedding,suppliedSubst,liftBind,varBind]
  exact ⟨(inst v) ▸ Derivation.equalityElimination clause (emb r) (emb v) same ((inst r).symm ▸ path)⟩

#print axioms pulledRename
#print axioms provideEarlier
#print axioms moveTarget
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOpenMatchedBindingProof
