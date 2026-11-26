module
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalGraphCompositionSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof InternalClosedPrograms
open InternalListInduction InternalListInductionSyntaxProof InternalRawListRecursionSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A closed contextual one-transition rule; all fresh-variable contexts
needed by the list-code induction are already included in its quantifiers. -/
def BackwardStep (transition test : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (initial out parameter : OTerm alpha),
  Nonempty (Derivation body Gamma (graph2 transition out initial parameter)) →
  Nonempty (Derivation body Gamma (graph2 test (suc z) out parameter)) →
  Nonempty (Derivation body Gamma (graph2 test (suc z) initial parameter))

/-- Initial state, output state and the SAME separate parameter are universally
bound inside the invariant. The raw list code is its only induction argument. -/
def backwardBody {alpha : Type} (transition test : Program 2) (code : OTerm alpha) :
    Formula (alpha ⊕ Fin 3) :=
  (repeatGraph transition (.var (.inr 1)) (code.relabel Sum.inl)
      (.var (.inr 0)) (.var (.inr 2)) ⊓
    graph2 test (suc z) (.var (.inr 1)) (.var (.inr 2))).imp
      (graph2 test (suc z) (.var (.inr 0)) (.var (.inr 2)))

def backwardRow {alpha : Type} (transition test : Program 2) (code : OTerm alpha) : Formula alpha :=
  allBlock (backwardBody transition test code)

theorem backwardRowSubst {alpha beta : Type} (transition test : Program 2)
    (code : OTerm alpha) (ts : alpha → OTerm beta) :
    (backwardRow transition test code).subst (fun a => emb (ts a)) =
      backwardRow transition test (code.subst ts) := by
  unfold backwardRow backwardBody
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,liftSubst,
    Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst]

theorem backwardRowRename {alpha beta : Type} (transition test : Program 2)
    (code : OTerm alpha) (j : alpha → beta) :
    (backwardRow transition test code).relabel j = backwardRow transition test (code.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (backwardRow transition test code).subst (fun a => emb (.var (j a))) = _
  rw [backwardRowSubst]
  simp only [← termRelabelAsSubst]

theorem backwardBodyWitness {alpha : Type} (transition test : Program 2)
    (code initial out parameter : OTerm alpha) :
    (backwardBody transition test code).subst
      (Sum.elim Term.var (fun i => emb (![initial,out,parameter] i))) =
      (repeatGraph transition out code initial parameter ⊓
        graph2 test (suc z) out parameter).imp (graph2 test (suc z) initial parameter) := by
  have he : (Sum.elim Term.var (fun i => emb (![initial,out,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![initial,out,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold backwardBody
  rw [he,impSubst,conjunctionSubst]
  simp only [graph2,programSubst,repeatSubst,consTermSubst,witnessLift,
    Term.subst,Sum.elim_inr,emptySubst,sucSubst,zSubst]
  rfl

theorem backwardAtCode {alpha : Type} (transition test : Program 2) (code : OTerm alpha) :
    atCode (backwardRow transition test (.var (.inr (0 : Fin 1)))) code =
      backwardRow transition test code := by
  simp only [atCode,instantiate,bindEmbedding,backwardRowSubst,varBind]

theorem backwardAtIndex {alpha : Type} (transition test : Program 2) (i : Fin 3) :
    atIndex (backwardRow transition test (.var (.inr (0 : Fin 1))) : Formula (alpha ⊕ Fin 1)) i =
      backwardRow transition test (.var (.inr i)) := by
  rw [atIndex,backwardRowRename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineRepeatSyntaxProof
