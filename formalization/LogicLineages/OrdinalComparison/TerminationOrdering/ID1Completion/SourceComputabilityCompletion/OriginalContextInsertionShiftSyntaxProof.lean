module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftSyntaxProof
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
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalContextInsertionVariableSupportProof

/-- Every output, requested type, actual prefix length, suffix, joined code,
and residual variable index is universally bound inside the induction row. -/
def shiftBody {alpha : Type} (front : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (lengthGraph (.var (.inr 2)) (front.relabel Sum.inl) ⊓
    graph2 InternalApplicationValidityStackAppend.append (.var (.inr 4))
      (front.relabel Sum.inl) (.var (.inr 3))).imp
    ((OriginalVariableDecoder.graph (.var (.inr 0)) (.var (.inr 1))
      (add (.var (.inr 2)) (.var (.inr 5))) (.var (.inr 4))).iff
      (OriginalVariableDecoder.graph (.var (.inr 0)) (.var (.inr 1))
        (.var (.inr 5)) (.var (.inr 3))))

def shiftRow {alpha : Type} (front : OTerm alpha) : Formula alpha := allBlock (shiftBody front)

 theorem shiftSubst {alpha beta : Type} (front : OTerm alpha) (ts : alpha → OTerm beta) :
    (shiftRow front).subst (fun a => emb (ts a)) = shiftRow (front.subst ts) := by
  unfold shiftRow shiftBody
  rw [allBlockSubst,liftedEmbedding]
  simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,lengthSubst,
    graph2Subst,variableSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

 theorem shiftRename {alpha beta : Type} (front : OTerm alpha) (j : alpha → beta) :
    (shiftRow front).relabel j = shiftRow (front.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (shiftRow front).subst (fun a => emb (.var (j a))) = _
  rw [shiftSubst]
  simp only [← termRelabelAsSubst]

 theorem shiftWitness {alpha : Type} (front out typ count suffix joined index : OTerm alpha) :
    (shiftBody front).subst
      (Sum.elim Term.var (fun i => emb (![out,typ,count,suffix,joined,index] i))) =
      (lengthGraph count front ⊓
        graph2 InternalApplicationValidityStackAppend.append joined front suffix).imp
        ((OriginalVariableDecoder.graph out typ (add count index) joined).iff
          (OriginalVariableDecoder.graph out typ index suffix)) := by
  have he : (Sum.elim Term.var (fun i => emb (![out,typ,count,suffix,joined,index] i))) =
      (fun a => emb (Sum.elim Term.var ![out,typ,count,suffix,joined,index] a)) := by
    funext a
    cases a <;> rfl
  unfold shiftBody
  rw [he]
  simp only [Formula.iff,BoundedFormula.iff,impSubst,conjunctionSubst,lengthSubst,
    graph2Subst,variableSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

 theorem shiftAtCode {alpha : Type} (front : OTerm alpha) :
    atCode (shiftRow (.var (.inr (0 : Fin 1)))) front = shiftRow front := by
  simp only [atCode,instantiate,bindEmbedding,shiftSubst,varBind]

 theorem shiftAtIndex {alpha : Type} (i : Fin 3) :
    atIndex (shiftRow (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      shiftRow (.var (.inr i)) := by
  rw [atIndex,shiftRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionShiftSyntaxProof
