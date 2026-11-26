module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding OTerm
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryPotentialCompletionSyntaxProof (emptyRename)
open InternalBinderTransportSyntaxProof (onTermRelabel formulaSubstVar)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem formulaLiftSubst {beta : Type} {k : Nat} (psi : Formula alpha) (ts : alpha → OTerm beta) :
 (psi.relabel (Sum.inl : alpha → alpha ⊕ Fin k)).subst
   (fun x => emb (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)) x)) =
 (psi.subst (fun a => emb (ts a))).relabel Sum.inl := by
 rw [actualRelabelSubstitution,formulaSubstRelabel]
 congr 1
 funext x
 exact onTermRelabel arithmeticEmbedding Sum.inl (ts x)
theorem formulaWitness {k : Nat} (psi : Formula alpha) (ts : Fin k → OTerm alpha) :
 (psi.relabel (Sum.inl : alpha → alpha ⊕ Fin k)).subst
   (fun x => emb (Sum.elim Term.var ts x)) = psi := by
 rw [actualRelabelSubstitution]
 change psi.subst Term.var = psi
 exact formulaSubstVar psi
def fields (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing input work results ⊓ (Agenda H M W c B work ⊓
 (graph2 InternalApplicationValidityStackAppend.append work front suffix ⊓
 (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input ⊓
 OriginalHereditaryPotentialCompletion.Empty output)))
def rowBody (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha) : Formula (alpha ⊕ Fin 4) :=
 (fields R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl)
   (output.relabel Sum.inl) (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))).imp
 (psi.relabel Sum.inl)
def row (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha) : Formula alpha :=
 allBlock (rowBody R H M W c B suffix output count psi)
theorem fieldsSubst {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields R H M W c B suffix output count input work results front).subst (fun x => emb (ts x)) =
 fields R H M W (c.subst ts) (B.subst ts) (suffix.subst ts) (output.subst ts) (count.subst ts)
   (input.subst ts) (work.subst ts) (results.subst ts) (front.subst ts) := by
 simp only [fields,conjunctionSubst,agendaSubst,OriginalHereditaryPotentialCompletion.Empty,
   graph2,graph1,programSubst,consTermSubst,emptySubst,InternalTagArithmeticSyntaxProof.zSubst]
theorem fieldsRename {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (j : alpha → beta) :
 (fields R H M W c B suffix output count input work results front).relabel j =
 fields R H M W (c.relabel j) (B.relabel j) (suffix.relabel j) (output.relabel j) (count.relabel j)
   (input.relabel j) (work.relabel j) (results.relabel j) (front.relabel j) := by
 simp only [fields,conjunctionRename,agendaRename,graph2Rename,OriginalHereditaryPotentialCompletionSyntaxProof.emptyRename]
theorem rowSubst {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha) (ts : alpha → OTerm beta) :
 (row R H M W c B suffix output count psi).subst (fun x => emb (ts x)) =
 row R H M W (c.subst ts) (B.subst ts) (suffix.subst ts) (output.subst ts) (count.subst ts)
   (psi.subst (fun x => emb (ts x))) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,liftSubst,Term.subst,Sum.elim_inr]
 rw [formulaLiftSubst]
theorem rowRename {beta : Type} (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha) (j : alpha → beta) :
 (row R H M W c B suffix output count psi).relabel j =
 row R H M W (c.relabel j) (B.relabel j) (suffix.relabel j) (output.relabel j) (count.relabel j) (psi.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row R H M W c B suffix output count psi).subst (fun x => emb (.var (j x))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst,← formulaRelabelAsSubst]
theorem rowBodyWitness (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (psi : Formula alpha) :
 (rowBody R H M W c B suffix output count psi).subst
   (Sum.elim Term.var (fun i => emb (![input,work,results,front] i))) =
 (fields R H M W c B suffix output count input work results front).imp psi := by
 have he : (Sum.elim Term.var (fun i => emb (![input,work,results,front] i))) =
   (fun x => emb (Sum.elim Term.var ![input,work,results,front] x)) := by
   funext x
   cases x <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,witnessLift,Term.subst,Sum.elim_inr]
 rw [formulaWitness]
theorem rowInstantiate (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm (alpha ⊕ Fin 1)) (psi : Formula (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row R H M W c B suffix output count psi) (emb t) =
 row R H M W (c.subst (bindTerm t)) (B.subst (bindTerm t)) (suffix.subst (bindTerm t))
   (output.subst (bindTerm t)) (count.subst (bindTerm t)) (psi.subst (fun a => emb (bindTerm t a))) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm (alpha ⊕ Fin 1)) (psi : Formula (alpha ⊕ Fin 1)) :
 successorInstance (row R H M W c B suffix output count psi) =
 row R H M W (c.subst nextTerm) (B.subst nextTerm) (suffix.subst nextTerm)
   (output.subst nextTerm) (count.subst nextTerm) (psi.subst (fun a => emb (nextTerm a))) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem formulaBind (psi : Formula alpha) (t : OTerm alpha) :
 (psi.relabel Sum.inl).subst (fun a => emb (bindTerm t a)) = psi := by
 exact formulaWitness psi (fun _ : Fin 1 => t)
theorem formulaNext (psi : Formula alpha) :
 (psi.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)).subst (fun a => emb (nextTerm a)) = psi.relabel Sum.inl := by
 rw [actualRelabelSubstitution,formulaRelabelAsSubst]
 rfl
theorem rowApply (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count input work results front : OTerm alpha) (psi : Formula alpha)
 (hr : Nonempty (Derivation body Delta (row R H M W c B suffix output count psi)))
 (hf : Nonempty (Derivation body Delta (fields R H M W c B suffix output count input work results front))) :
 Nonempty (Derivation body Delta psi) := by
 have h := actualFiniteUniversalElimination body alpha 4 Delta (rowBody R H M W c B suffix output count psi)
   (fun i => emb (![input,work,results,front] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitSyntax
