module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedCallsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedForwardBindingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open SourceComputabilityFormulaSupportProof (existsOne)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn bindEmbedding liftBind varBind)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseLeastSubstitutionThinProof (leastSubst)
open NumberedWindowInternalSparsePositiveTransitivityTargets (supplied)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (suppliedSubst suppliedRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)

def pushed (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    {α : Type} (ctx cod parent earlier : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let later : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  existsOne (leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) later ⊓
    supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) (earlier.relabel j) later)

theorem pushedRename {α β : Type} (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (raw : Program 5) (ctx cod parent earlier : OTerm α) (j : α → β) :
    (pushed C X W s raw ctx cod parent earlier).relabel j =
      pushed C X W s raw (ctx.relabel j) (cod.relabel j) (parent.relabel j) (earlier.relabel j) := by
  simp only [pushed,existsRename,conjunctionRename,leastRename,suppliedRename,Term.relabel_relabel,Term.relabel]
  rfl

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem provideLater (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)
    (ctx cod parent earlier later : OTerm α)
    (found : Derivation B Γ (leastGraph C X W s ctx cod parent later))
    (path : Derivation B Γ (supplied raw (packedLeastProgram C X W s) ctx cod earlier later)) :
    Nonempty (Derivation B Γ (pushed C X W s raw ctx cod parent earlier)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let clause := leastGraph C X W s (ctx.relabel j) (cod.relabel j) (parent.relabel j) x ⊓
    supplied raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) (earlier.relabel j) x
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (phi := clause) (emb later)
  simp only [clause,j,x,instantiate,bindEmbedding,conjunctionSubst,leastSubst,suppliedSubst,liftBind,varBind]
  exact Derivation.conjunctionIntroduction found path

theorem moveSource (raw : Program 5) (least : Program 3) (ctx cod a a' dst : OTerm α)
    (same : Derivation B Γ (eqn a a')) (path : Derivation B Γ (supplied raw least ctx cod a dst)) :
    Nonempty (Derivation B Γ (supplied raw least ctx cod a' dst)) := by
  let clause : Formula (α ⊕ Fin 1) := supplied raw least (ctx.relabel Sum.inl) (cod.relabel Sum.inl)
    (.var (.inr 0)) (dst.relabel Sum.inl)
  have inst (t : OTerm α) : instantiate clause (emb t) = supplied raw least ctx cod t dst := by
    simp only [clause,instantiate,bindEmbedding,suppliedSubst,liftBind,varBind]
  exact ⟨(inst a') ▸ Derivation.equalityElimination clause (emb a) (emb a') same ((inst a).symm ▸ path)⟩

#print axioms pushedRename
#print axioms provideLater
#print axioms moveSource
end LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedForwardBindingProof
