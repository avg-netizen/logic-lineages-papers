module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof InternalRawListRecursionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalAdditionLawsProof
open InternalListInduction InternalListInductionSyntaxProof
open InternalOriginalOrderSyntaxProof InternalQuotientComparisonSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof

/-- Below the actual length of a raw front, appending any suffix retains
its complete original variable-checker graph, with every output bound. -/
def belowBody {alpha : Type} (front : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (lengthGraph (.var (.inr 2)) (front.relabel Sum.inl) ⊓
    (graph2 InternalApplicationValidityStackAppend.append (.var (.inr 4))
      (front.relabel Sum.inl) (.var (.inr 3)) ⊓
      ltF (.var (.inr 5)) (.var (.inr 2)))).imp
    ((OriginalVariableDecoder.graph (.var (.inr 0)) (.var (.inr 1))
      (.var (.inr 5)) (.var (.inr 4))).iff
      (OriginalVariableDecoder.graph (.var (.inr 0)) (.var (.inr 1))
        (.var (.inr 5)) (front.relabel Sum.inl)))

def belowRow {alpha : Type} (front : OTerm alpha) : Formula alpha := allBlock (belowBody front)

 theorem belowSubst {alpha beta : Type} (front : OTerm alpha) (ts : alpha → OTerm beta) :
    (belowRow front).subst (fun a => emb (ts a)) = belowRow (front.subst ts) := by
  unfold belowRow belowBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,lengthSubst,
    graph2Subst,variableSubst,orderSubst,liftSubst,Term.subst,Sum.elim_inr]

 theorem belowRename {alpha beta : Type} (front : OTerm alpha) (j : alpha → beta) :
    (belowRow front).relabel j = belowRow (front.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (belowRow front).subst (fun a => emb (.var (j a))) = _
  rw [belowSubst]
  simp only [← termRelabelAsSubst]

 theorem belowWitness {alpha : Type} (front out typ count suffix joined index : OTerm alpha) :
    (belowBody front).subst
      (Sum.elim Term.var (fun i => emb (![out,typ,count,suffix,joined,index] i))) =
      (lengthGraph count front ⊓
        (graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
          ltF index count)).imp
        ((OriginalVariableDecoder.graph out typ index joined).iff
          (OriginalVariableDecoder.graph out typ index front)) := by
  have he : (Sum.elim Term.var (fun i => emb (![out,typ,count,suffix,joined,index] i))) =
      (fun a => emb (Sum.elim Term.var ![out,typ,count,suffix,joined,index] a)) := by
    funext a
    cases a <;> rfl
  unfold belowBody
  rw [he]
  simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,lengthSubst,
    graph2Subst,variableSubst,orderSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

 theorem belowAtCode {alpha : Type} (front : OTerm alpha) :
    atCode (belowRow (.var (.inr (0 : Fin 1)))) front = belowRow front := by
  simp only [atCode,instantiate,bindEmbedding,belowSubst,varBind]

 theorem belowAtIndex {alpha : Type} (i : Fin 3) :
    atIndex (belowRow (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      belowRow (.var (.inr i)) := by
  rw [atIndex,belowRename]
  rfl

 theorem iffRename {alpha beta : Type} (p q : Formula alpha) (j : alpha → beta) :
    (p.iff q).relabel j = (p.relabel j).iff (q.relabel j) := rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowSyntaxProof
