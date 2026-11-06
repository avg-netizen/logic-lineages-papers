module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalAdditionLawsProof
open InternalFiniteBlocksBindingProof InternalDerivationRenamingSyntaxProof InternalDerivationRenamingArithmeticProof

/-- Only an abbreviation for the ORIGINAL embedded formula, not a relation symbol. -/
abbrev ltF {α : Type} (s t : OTerm α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula s t)

def witnessBody {α : Type} (s t : OTerm α) : Formula (α ⊕ Fin 1) :=
  eqn (add (s.relabel Sum.inl) (suc (.var (.inr 0)))) (t.relabel Sum.inl)

theorem actualOriginalOrderEmbedding : InternalOriginalOrderTargets.ActualOriginalOrderEmbedding := by
  intro α s t
  unfold OrdinaryArithmetic.lessFormula
  rw [actualOriginalBlockEmbedding]
  rfl

theorem embedding {α : Type} (s t : OTerm α) : ltF s t = existsOne (witnessBody s t) := by
  unfold ltF
  rw [actualOriginalOrderEmbedding]
  congr 1
  rw [onEquality]
  rfl

theorem witnessInstantiate {α : Type} (s t w : OTerm α) :
    instantiate (witnessBody s t) (emb w) = eqn (add s (suc w)) t := by
  simp only [witnessBody,eqnInstantiate,addSubst,sucSubst,liftBind,varBind]

theorem addRelabel {α β : Type} (s t : OTerm α) (h : α → β) :
    (add s t).relabel h = add (s.relabel h) (t.relabel h) := binaryRelabel _ _ _ _

theorem orderRename {α β : Type} (s t : OTerm α) (h : α → β) :
    (ltF s t).relabel h = ltF (s.relabel h) (t.relabel h) := by
  rw [embedding,existsRename,embedding]
  congr 1
  unfold witnessBody
  rw [eqnRelabel]
  simp only [addRelabel,sucRelabel,Term.relabel_relabel,Term.relabel]
  rfl

@[simp] theorem notInstantiate {α : Type} (p : Formula (α ⊕ Fin 1)) (t : Term α) :
    instantiate p.not t = (instantiate p t).not := rfl
@[simp] theorem notSubst {α β : Type} (p : Formula α) (ts : α → Term β) :
    p.not.subst ts = (p.subst ts).not := rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
