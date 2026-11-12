module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalTypedArgumentObservations
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def terminalBody (R : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
 (InternalLessThan.strictLess (.var (.inr 0)) (count.relabel Sum.inl)).imp
 ((graph2 InternalPairing.pairing (.var (.inr 2)) (.var (.inr 0)) (.var (.inr 1))).imp
 ((graph3 (walk R) (.var (.inr 4)) (count.relabel Sum.inl) (.var (.inr 2)) (.var (.inr 3))).imp
   (graph2 (walkStep R) (.var (.inr 4)) (.var (.inr 4)) (.var (.inr 3)))))
def terminalRow (R : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (terminalBody R count)

theorem terminalSubst {beta : Type} (R : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (terminalRow R count).subst (fun a => emb (ts a)) = terminalRow R (count.subst ts) := by
 unfold terminalRow terminalBody graph2 graph3
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst,
   InternalLessThan.strictLess,orderSubst]

theorem terminalRename {beta : Type} (R : Program 2) (count : OTerm alpha) (j : alpha → beta) :
 (terminalRow R count).relabel j = terminalRow R (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (terminalRow R count).subst (fun a => emb (.var (j a))) = _
 rw [terminalSubst]
 simp only [← termRelabelAsSubst]

theorem terminalWitness (R : Program 2) (count raw acc initial parameter out : OTerm alpha) :
 (terminalBody R count).subst (Sum.elim Term.var (fun i => emb (![raw,acc,initial,parameter,out] i))) =
 (InternalLessThan.strictLess raw count).imp
 ((graph2 InternalPairing.pairing initial raw acc).imp
 ((graph3 (walk R) out count initial parameter).imp (graph2 (walkStep R) out out parameter))) := by
 have he : (Sum.elim Term.var (fun i => emb (![raw,acc,initial,parameter,out] i))) =
   (fun a => emb (Sum.elim Term.var ![raw,acc,initial,parameter,out] a)) := by
   funext a
   cases a <;> rfl
 unfold terminalBody graph2 graph3
 rw [he]
 simp only [impSubst,programSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst,
   InternalLessThan.strictLess,orderSubst]
 rfl

theorem terminalInstantiate (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (terminalRow R count) (emb t) = terminalRow R (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,terminalSubst]
theorem terminalSuccessor (R : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (terminalRow R count) = terminalRow R (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,terminalSubst]

theorem terminalApply (R : Program 2) (count raw acc initial parameter out : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (terminalRow R count)))
 (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess raw count)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing initial raw acc)))
 (hr : Nonempty (Derivation body Delta (graph3 (walk R) out count initial parameter))) :
 Nonempty (Derivation body Delta (graph2 (walkStep R) out out parameter)) := by
 have h := actualFiniteUniversalElimination body alpha 5 Delta (terminalBody R count)
   (fun i => emb (![raw,acc,initial,parameter,out] i)) hrow
 rw [terminalWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hb⟩ := hb
 obtain ⟨hp⟩ := hp
 obtain ⟨hr⟩ := hr
 exact ⟨Derivation.implicationElimination (Derivation.implicationElimination
   (Derivation.implicationElimination h hb) hp) hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsTerminationSyntaxProof
