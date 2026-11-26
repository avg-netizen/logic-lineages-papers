module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveSentenceProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (eqn emb bindTerm bindEmbedding liftBind varBind sucSubst zSubst eqnInstantiate eqnRelabel sucRelabel)
open ID1Completion.InternalAdditionLawsProof (addSubst)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral existsOne)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralSingletonBoundMachineProof
open NumberedWindowInternalLiteralSingletonBoundOpenRowsProof
open NumberedWindowInternalLiteralSingletonBoundOpenAboveExistenceProof
  (boundTermRename exact_OpenSingletonBoundAboveCases)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-! ### Reusable syntax: instantiation and substitution -/

/-- Instantiation of the bound variable commutes with conjunction. -/
theorem conjunctionInstantiate (p q : Formula (α ⊕ Fin 1)) (t : Term α) :
    instantiate (p ⊓ q) t = instantiate p t ⊓ instantiate q t := rfl

/-- Instantiating the bound variable of an actual program graph substitutes
in its output and in every input. The program is arbitrary. -/
theorem programInstantiate {n : Nat} (p : Program n) (out : OTerm (α ⊕ Fin 1))
    (xs : Fin n → OTerm (α ⊕ Fin 1)) (u : OTerm α) :
    instantiate (programGraph p out xs) (emb u) =
      programGraph p (out.subst (bindTerm u)) (fun k => (xs k).subst (bindTerm u)) := by
  rw [instantiate,bindEmbedding]
  unfold programGraph
  exact graphSubst _ out xs (bindTerm u)

theorem tripleInputsSubst {β : Type} (x y w : OTerm α) (ts : α → OTerm β) :
    (fun k : Fin 3 => ((![x,y,w] : Fin 3 → OTerm α) k).subst ts) =
      ![x.subst ts,y.subst ts,w.subst ts] := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l =>
    Fin.cases ?_ (fun u => Fin.elim0 u) l) k) k <;> rfl

private theorem mulTermSubst {β : Type} (s t : OTerm α) (ts : α → OTerm β) :
    (OrdinaryArithmetic.mulTerm s t).subst ts =
      OrdinaryArithmetic.mulTerm (s.subst ts) (t.subst ts) :=
  ID1Completion.InternalSourceInversionSupportProof.applyTwoSubstitution _ _ _ _

private theorem numeralSubst {β : Type} (n : Nat) (ts : α → OTerm β) :
    (numeral n : OTerm α).subst ts = numeral n := by
  induction n with
  | zero => exact zSubst ts
  | succ n ih =>
    simpa only [numeral,sucSubst] using
      congrArg ID1Completion.InternalTagArithmeticSyntaxProof.suc ih

theorem rawConsSubst {β : Type} (x y : OTerm α) (ts : α → OTerm β) :
    (rawCons x y).subst ts = rawCons (x.subst ts) (y.subst ts) := by
  unfold rawCons pairTerm
  simp only [sucSubst,addSubst,mulTermSubst]

theorem packedBodySubst {β : Type} (xs : List (OTerm α)) (ts : α → OTerm β) :
    (packedBody xs).subst ts = packedBody (xs.map (fun t => t.subst ts)) := by
  induction xs with
  | nil => exact zSubst ts
  | cons x xs ih => simp only [packedBody,rawConsSubst,ih,List.map_cons]

/-- The packed bound node commutes with term substitution. -/
theorem boundTermSubst {β : Type} (t i : OTerm α) (ts : α → OTerm β) :
    (boundTerm t i).subst ts = boundTerm (t.subst ts) (i.subst ts) := by
  simp only [boundTerm,rawConsSubst,packedBodySubst,numeralSubst,List.map_cons,List.map_nil]

private theorem conjunctionRelabel {β : Type} (p q : Formula α) (f : α → β) :
    (p ⊓ q).relabel f = p.relabel f ⊓ q.relabel f := rfl

private theorem liftedRename {β : Type} (x : OTerm α) (r : α → β) :
    (x.relabel (Sum.inl : α → α ⊕ Fin 1)).relabel (Sum.map r (id : Fin 1 → Fin 1)) =
      (x.relabel r).relabel (Sum.inl : β → β ⊕ Fin 1) := by
  rw [Term.relabel_relabel,Term.relabel_relabel]
  rfl

private theorem liftedVariable {β : Type} (r : α → β) :
    (Term.var (Sum.inr 0) : OTerm (α ⊕ Fin 1)).relabel (Sum.map r (id : Fin 1 → Fin 1)) =
      (Term.var (Sum.inr 0) : OTerm (β ⊕ Fin 1)) := rfl

/-! ### The sentence -/

/-- Matrix of the existence sentence. The bound variable is the lowered
index: the original index is its successor, and the actual `singletonBound`
graph on the original tape has the packed node at that variable as output. -/
def aboveBody (V : Program 1) (H : Program 2) (U : Program 3) (a d t i : OTerm α) :
    Formula (α ⊕ Fin 1) :=
  (eqn (i.relabel Sum.inl) (suc (Term.var (Sum.inr 0))) : Formula (α ⊕ Fin 1)) ⊓
    (programGraph (singletonBound V H U)
      (suc (boundTerm (t.relabel Sum.inl) (Term.var (Sum.inr 0))))
      ![a.relabel Sum.inl,d.relabel Sum.inl,boundTerm (t.relabel Sum.inl) (i.relabel Sum.inl)] :
      Formula (α ⊕ Fin 1))

/-- Object-language existence of the lowered result. -/
def aboveResult (V : Program 1) (H : Program 2) (U : Program 3) (a d t i : OTerm α) :
    Formula α :=
  existsOne (aboveBody V H U a d t i)

theorem aboveBodyInstantiate (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i j : OTerm α) :
    instantiate (aboveBody V H U a d t i) (emb j) =
      eqn i (suc j) ⊓ programGraph (singletonBound V H U) (suc (boundTerm t j))
        ![a,d,boundTerm t i] := by
  unfold aboveBody
  simp only [conjunctionInstantiate,eqnInstantiate,programInstantiate,tripleInputsSubst,
    sucSubst,boundTermSubst,liftBind,varBind]

theorem aboveBodyRename {β : Type} (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (r : α → β) :
    (aboveBody V H U a d t i).relabel (Sum.map r id) =
      aboveBody V H U (a.relabel r) (d.relabel r) (t.relabel r) (i.relabel r) := by
  unfold aboveBody
  simp only [conjunctionRelabel,eqnRelabel,programRename,tripleInputsRename,sucRelabel,
    boundTermRename,liftedRename,liftedVariable]

theorem aboveResultRename {β : Type} (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (r : α → β) :
    (aboveResult V H U a d t i).relabel r =
      aboveResult V H U (a.relabel r) (d.relabel r) (t.relabel r) (i.relabel r) := by
  unfold aboveResult
  rw [existsRename,aboveBodyRename]

attribute [local irreducible] programGraph

/-- Above the substitution depth the open arithmetic context derives the
existence sentence itself. The witness is the object term produced by the
order elimination in `exact_OpenSingletonBoundAboveCases`; it is introduced
by the calculus rule for the existential quantifier. Both original syntax
guards and the order derivation are the only premises. -/
theorem exact_OpenSingletonBoundAboveExists (V : Program 1) (H : Program 2) (U : Program 3)
    (a d t i : OTerm α) (inserted : D B Γ (unary V (suc z) a))
    (typedNode : D B Γ (unary V (suc z) (boundTerm t i)))
    (above : D B Γ (ltF d i)) :
    D B Γ (aboveResult V H U a d t i) := by
  apply exact_OpenSingletonBoundAboveCases V H U a d t i (aboveResult V H U a d t i)
    inserted typedNode above
  intro β r Δ j keep same graph
  rw [aboveResultRename]
  obtain ⟨same⟩ := same
  obtain ⟨graph⟩ := graph
  unfold aboveResult
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb j)
  rw [aboveBodyInstantiate]
  exact Derivation.conjunctionIntroduction same graph

#print axioms conjunctionInstantiate
#print axioms programInstantiate
#print axioms tripleInputsSubst
#print axioms rawConsSubst
#print axioms packedBodySubst
#print axioms boundTermSubst
#print axioms aboveBodyInstantiate
#print axioms aboveBodyRename
#print axioms aboveResultRename
#print axioms exact_OpenSingletonBoundAboveExists
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonBoundOpenAboveSentenceProof
