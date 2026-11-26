module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceElimination
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb suc)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open CodedDeletionTraceDefinitions CodedDeletionTraceSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem stateInstantiate (trace index left right parameter gamma entry : OTerm alpha) :
 instantiate (stateMatrix trace index left right parameter gamma) (emb entry) =
 (graph2 InternalRawListRecursion.lookup entry index trace ⊓ StateFields entry left right parameter gamma) := by
 rw [instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding]
 unfold stateMatrix
 simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,fieldsSubst,
   InternalTagArithmeticSyntaxProof.varBind,InternalTagArithmeticSyntaxProof.liftBind]
theorem stateIntro (trace index left right parameter gamma entry : OTerm alpha)
 (h : Nonempty (Derivation body Delta
   (graph2 InternalRawListRecursion.lookup entry index trace ⊓ StateFields entry left right parameter gamma))) :
 Nonempty (Derivation body Delta (StateAt trace index left right parameter gamma)) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialIntroduction (emb entry)
 rw [stateInstantiate]
 exact h
theorem stateCases (trace index left right parameter gamma : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (StateAt trace index left right parameter gamma)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (entry : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
     (graph2 InternalRawListRecursion.lookup entry (index.relabel j) (trace.relabel j) ⊓
      StateFields entry (left.relabel j) (right.relabel j) (parameter.relabel j) (gamma.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 obtain ⟨h⟩ := h
 apply Nonempty.intro
 apply Derivation.existentialElimination h
 exact Classical.choice (next (alpha ⊕ Fin 1) Sum.inl
   (stateMatrix trace index left right parameter gamma :: Delta.map weaken) (.var (.inr 0))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩)
def StepFields (trace index c : OTerm alpha) (v : Fin 13 → OTerm alpha) : Formula alpha :=
 graph2 InternalRawListRecursion.lookup (v 0) index trace ⊓
 (graph2 InternalRawListRecursion.lookup (v 1) (suc index) trace ⊓
 (StateFields (v 0) (v 2) (v 3) (v 4) (v 5) ⊓
 (Metadata (v 0) (v 6) (v 7) (v 8) ⊓
 (StateFields (v 1) (v 9) (v 10) (v 11) (v 12) ⊓
 DeletionChainDefinitions.Transition (v 2) (v 3) (v 9) (v 10) (v 4) (v 11)
   c (v 5) (v 12) (v 6) (v 7) (v 8)))))
theorem stepCases (trace index c : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (StepAt trace index c)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (v : Fin 13 → OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (StepFields (trace.relabel j) (index.relabel j) (c.relabel j) v)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let P := stepMatrix trace index c
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 13 Delta P psi h
 exact next (alpha ⊕ Fin 13) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
   (fun i => .var (.inr i))
   (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
   ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem allWitness (trace steps c index : OTerm alpha) :
 (stepsBody trace steps c).subst (Sum.elim Term.var (fun _ => emb index)) =
 (OriginalContextInsertion.Below index steps).imp (StepAt trace index c) := by
 have he : (Sum.elim Term.var (fun _ : Fin 1 => emb index)) =
   (fun a => emb (Sum.elim Term.var (fun _ : Fin 1 => index) a)) := by funext a; cases a <;> rfl
 unfold stepsBody
 rw [he,impSubst]
 simp only [OriginalContextInsertion.Below,orderSubst,stepSubst,witnessLift,Term.subst,Sum.elim_inr]
theorem allApply (trace steps c index : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AllSteps trace steps c)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index steps))) :
 Nonempty (Derivation body Delta (StepAt trace index c)) := by
 have h := actualFiniteUniversalElimination body alpha 1 Delta (stepsBody trace steps c) (fun _ => emb index) ha
 rw [allWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hb⟩ := hb
 exact ⟨Derivation.implicationElimination h hb⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceElimination
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceElimination
