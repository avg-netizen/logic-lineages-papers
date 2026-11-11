module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
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
open OriginalHereditaryValidityInternalRecurrence

@[simp] theorem fuelSubst {alpha beta : Type} (count code : OTerm alpha) (ts : alpha → OTerm beta) :
    (WorkFuelGraph count code).subst (fun a => emb (ts a)) =
      WorkFuelGraph (count.subst ts) (code.subst ts) := by
  simp only [WorkFuelGraph,graph1,programSubst,consTermSubst,emptySubst]

/-- The front code is the induction parameter. Every suffix, joined code,
and both actual weights are bound inside the invariant. -/
def fuelAppendBody {alpha : Type} (front : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  (graph2 InternalApplicationValidityStackAppend.append (.var (.inr 1))
      (front.relabel Sum.inl) (.var (.inr 0)) ⊓
    (WorkFuelGraph (.var (.inr 2)) (front.relabel Sum.inl) ⊓
      WorkFuelGraph (.var (.inr 3)) (.var (.inr 0)))).imp
    (WorkFuelGraph (add (.var (.inr 2)) (.var (.inr 3))) (.var (.inr 1)))

def fuelAppendRow {alpha : Type} (front : OTerm alpha) : Formula alpha :=
  allBlock (fuelAppendBody front)

 theorem fuelAppendSubst {alpha beta : Type} (front : OTerm alpha) (ts : alpha → OTerm beta) :
    (fuelAppendRow front).subst (fun a => emb (ts a)) = fuelAppendRow (front.subst ts) := by
  unfold fuelAppendRow fuelAppendBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,fuelSubst,addSubst,liftSubst,Term.subst,Sum.elim_inr]

 theorem fuelAppendRename {alpha beta : Type} (front : OTerm alpha) (j : alpha → beta) :
    (fuelAppendRow front).relabel j = fuelAppendRow (front.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (fuelAppendRow front).subst (fun a => emb (.var (j a))) = _
  rw [fuelAppendSubst]
  simp only [← termRelabelAsSubst]

 theorem fuelAppendWitness {alpha : Type} (front suffix joined first second : OTerm alpha) :
    (fuelAppendBody front).subst
      (Sum.elim Term.var (fun i => emb (![suffix,joined,first,second] i))) =
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
        (WorkFuelGraph first front ⊓ WorkFuelGraph second suffix)).imp
        (WorkFuelGraph (add first second) joined) := by
  have he : (Sum.elim Term.var (fun i => emb (![suffix,joined,first,second] i))) =
      (fun a => emb (Sum.elim Term.var ![suffix,joined,first,second] a)) := by
    funext a
    cases a <;> rfl
  unfold fuelAppendBody
  rw [he,impSubst,conjunctionSubst,conjunctionSubst]
  simp only [graph2Subst,fuelSubst,addSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

 theorem fuelAppendAtCode {alpha : Type} (front : OTerm alpha) :
    atCode (fuelAppendRow (.var (.inr (0 : Fin 1)))) front = fuelAppendRow front := by
  simp only [atCode,instantiate,bindEmbedding,fuelAppendSubst,varBind]

 theorem fuelAppendAtIndex {alpha : Type} (i : Fin 3) :
    atIndex (fuelAppendRow (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      fuelAppendRow (.var (.inr i)) := by
  rw [atIndex,fuelAppendRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelAppendSyntaxProof
