module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixNonzeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalListInduction InternalListInductionSyntaxProof InternalRawListRecursionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Universal endpoint/parameter row; only the original list code is the
induction variable. The original positive checker, window and guard remain
literal arithmetic Programs. -/
def spineBody {alpha : Type} (edge : Program 4) (window : Program 1) (code : OTerm alpha) :
    Formula (alpha ⊕ Fin 3) :=
  (graph2 (BottomRepresentative.windowAt window) (suc z) (.var (.inr 0)) (.var (.inr 2)) ⊓
    graph4 (InternalParameterizedPathChecker.checker edge true) (suc z)
      (.var (.inr 0)) (.var (.inr 1)) (code.relabel Sum.inl) (.var (.inr 2))).imp
    (OriginalSpineGuardLeaf.spineAccepted (.var (.inr 0)) (.var (.inr 1))
      (code.relabel Sum.inl) (.var (.inr 2)))

def spineRow {alpha : Type} (edge : Program 4) (window : Program 1) (code : OTerm alpha) : Formula alpha :=
  allBlock (spineBody edge window code)

theorem spineRowSubst {alpha beta : Type} (edge : Program 4) (window : Program 1)
    (code : OTerm alpha) (ts : alpha → OTerm beta) :
    (spineRow edge window code).subst (fun a => emb (ts a)) =
      spineRow edge window (code.subst ts) := by
  unfold spineRow spineBody OriginalSpineGuardLeaf.spineAccepted
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [graph2,graph4,programSubst,consTermSubst,liftSubst,
    Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst,InternalOriginalStepGuard.one]

theorem spineRowRename {alpha beta : Type} (edge : Program 4) (window : Program 1)
    (code : OTerm alpha) (j : alpha → beta) :
    (spineRow edge window code).relabel j = spineRow edge window (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (spineRow edge window code).subst (fun a => emb (.var (j a))) = _
  rw [spineRowSubst]
  simp only [← termRelabelAsSubst]

theorem spineBodyWitness {alpha : Type} (edge : Program 4) (window : Program 1)
    (code x y parameter : OTerm alpha) :
    (spineBody edge window code).subst
      (Sum.elim Term.var (fun i => emb (![x,y,parameter] i))) =
      (OriginalFunctionNeutrality.windowGraph window x parameter ⊓
        InternalParameterizedPathChecker.positiveGraph edge x y code parameter).imp
        (OriginalSpineGuardLeaf.spineAccepted x y code parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![x,y,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![x,y,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold spineBody OriginalSpineGuardLeaf.spineAccepted
  rw [he,impSubst,conjunctionSubst]
  simp only [graph2,graph4,programSubst,consTermSubst,witnessLift,
    Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst,InternalOriginalStepGuard.one]
  rfl

theorem spineAtCode {alpha : Type} (edge : Program 4) (window : Program 1) (code : OTerm alpha) :
    atCode (spineRow edge window (.var (.inr (0 : Fin 1)))) code =
      spineRow edge window code := by
  simp only [atCode,instantiate,bindEmbedding,spineRowSubst,varBind]

theorem spineAtIndex {alpha : Type} (edge : Program 4) (window : Program 1) (i : Fin 3) :
    atIndex (spineRow edge window (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      spineRow edge window (.var (.inr i)) := by
  rw [atIndex,spineRowRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixInductionSyntaxProof
