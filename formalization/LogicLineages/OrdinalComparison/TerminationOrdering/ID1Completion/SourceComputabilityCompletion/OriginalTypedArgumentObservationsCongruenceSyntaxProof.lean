module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceSyntaxProof
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
open OriginalTypedArgumentObservations OriginalTypedDecoderInternalLogicSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalTypedArgumentObservationsCongruence OriginalUniverseDecoderInternalFuelNumericSyntaxProof
theorem agreementSubst {beta : Type} (R S : Program 2) (parameter : OTerm alpha) (ts : alpha → OTerm beta) :
 (Agreement R S parameter).subst (fun a => emb (ts a)) = Agreement R S (parameter.subst ts) := by
 unfold Agreement agreementBody graph2
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,conjunctionSubst,equalSubst,programSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem agreementRename {beta : Type} (R S : Program 2) (parameter : OTerm alpha) (j : alpha → beta) :
 (Agreement R S parameter).relabel j = Agreement R S (parameter.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Agreement R S parameter).subst (fun a => emb (.var (j a))) = _
 rw [agreementSubst]
 simp only [← termRelabelAsSubst]

theorem agreementWitness (R S : Program 2) (parameter input left right : OTerm alpha) :
 (agreementBody R S parameter).subst (Sum.elim Term.var (fun i => emb (![input,left,right] i))) =
 (graph2 R left input parameter ⊓ graph2 S right input parameter).imp (equal left right) := by
 have he : (Sum.elim Term.var (fun i => emb (![input,left,right] i))) =
   (fun a => emb (Sum.elim Term.var ![input,left,right] a)) := by
   funext a
   cases a <;> rfl
 unfold agreementBody graph2
 rw [he]
 simp only [impSubst,conjunctionSubst,equalSubst,programSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst]
 rfl

theorem agreementApply (R S : Program 2) (parameter input left right : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (hl : Nonempty (Derivation body Delta (graph2 R left input parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 S right input parameter))) :
 Nonempty (Derivation body Delta (equal left right)) := by
 have h := actualFiniteUniversalElimination body alpha 3 Delta (agreementBody R S parameter)
   (fun i => emb (![input,left,right] i)) ha
 rw [agreementWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hl⟩ := hl
 obtain ⟨hr⟩ := hr
 exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hl hr)⟩

def iterationBody (R S : Program 2) (count : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
 (Agreement R S (.var (.inr 1))).imp ((repeatGraph R (.var (.inr 2)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp ((repeatGraph S (.var (.inr 3)) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))).imp (equal (.var (.inr 2)) (.var (.inr 3)))))
def iterationRow (R S : Program 2) (count : OTerm alpha) : Formula alpha := allBlock (iterationBody R S count)

theorem iterationSubst {beta : Type} (R S : Program 2) (count : OTerm alpha) (ts : alpha → OTerm beta) :
 (iterationRow R S count).subst (fun a => emb (ts a)) = iterationRow R S (count.subst ts) := by
 unfold iterationRow iterationBody
 rw [allBlockSubst,liftedEmbedding]
 simp only [impSubst,equalSubst,agreementSubst,repeatSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem iterationRename {beta : Type} (R S : Program 2) (count : OTerm alpha) (j : alpha → beta) :
 (iterationRow R S count).relabel j = iterationRow R S (count.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (iterationRow R S count).subst (fun a => emb (.var (j a))) = _
 rw [iterationSubst]
 simp only [← termRelabelAsSubst]

theorem iterationWitness (R S : Program 2) (count initial parameter left right : OTerm alpha) :
 (iterationBody R S count).subst (Sum.elim Term.var (fun i => emb (![initial,parameter,left,right] i))) =
 (Agreement R S parameter).imp ((repeatGraph R left count initial parameter).imp ((repeatGraph S right count initial parameter).imp (equal left right))) := by
 have he : (Sum.elim Term.var (fun i => emb (![initial,parameter,left,right] i))) =
   (fun a => emb (Sum.elim Term.var ![initial,parameter,left,right] a)) := by
   funext a
   cases a <;> rfl
 unfold iterationBody
 rw [he]
 simp only [impSubst,equalSubst,agreementSubst,repeatSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl

theorem iterationInstantiate (R S : Program 2) (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (iterationRow R S count) (emb t) = iterationRow R S (count.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,iterationSubst]
theorem iterationSuccessor (R S : Program 2) (count : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (iterationRow R S count) = iterationRow R S (count.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,iterationSubst]

theorem iterationApply (R S : Program 2) (count initial parameter left right : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (iterationRow R S count)))
 (h0 : Nonempty (Derivation body Delta (Agreement R S parameter)))
 (h1 : Nonempty (Derivation body Delta (repeatGraph R left count initial parameter)))
 (h2 : Nonempty (Derivation body Delta (repeatGraph S right count initial parameter)))
 : Nonempty (Derivation body Delta (equal left right)) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (iterationBody R S count)
   (fun i => emb (![initial,parameter,left,right] i)) hrow
 rw [iterationWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨h0⟩ := h0
 obtain ⟨h1⟩ := h1
 obtain ⟨h2⟩ := h2
 exact ⟨Derivation.implicationElimination (Derivation.implicationElimination (Derivation.implicationElimination h h0) h1) h2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsCongruenceSyntaxProof
