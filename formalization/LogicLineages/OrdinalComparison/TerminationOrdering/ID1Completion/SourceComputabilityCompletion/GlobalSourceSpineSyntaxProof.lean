module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open Source (Ty)
open InternalApplicationCertificateConstructors
open InternalComputabilityApplication InternalComputabilityApplicationSyntaxProof
open InternalAccessibilityRules
open InternalAccessibilityRulesSyntaxProof (membershipSubst)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalClosedPrograms InternalClosedProgramsBindingProof SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof (OTerm emb z suc sucSubst zSubst bindTerm bindEmbedding)
open InternalAdditionLawsProof (impSubst)
open SourceComputabilityCompletion.TypedSpine

theorem typedSubst {α β : Type} (comp : JointGammaComputability.Data) (tau : Ty)
    (context x : OTerm α) (ts : α → OTerm β) :
    (typed comp tau context x).subst (fun a => emb (ts a)) =
      typed comp tau (context.subst ts) (x.subst ts) := by
  unfold InternalComputabilityApplication.typed
  rw [programSubst,sucSubst,zSubst]
  congr 1
  funext i
  exact Fin.cases rfl (Fin.cases (numeralSubst _ ts)
    (Fin.cases rfl (fun q => Fin.elim0 q))) i

theorem unarySubst {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1)
    (out x : OTerm α) (ts : α → OTerm β) :
    (graph1 p out x).subst (fun a => emb (ts a)) = graph1 p (out.subst ts) (x.subst ts) := by
  simp only [graph1,programSubst,consTermSubst,emptySubst]

theorem markedSubst {α β : Type} (x mark depth : OTerm α) (ts : α → OTerm β) :
    (marked x mark depth).subst (fun a => emb (ts a)) =
      marked (x.subst ts) (mark.subst ts) (depth.subst ts) := by
  simp only [marked,conjunctionSubst,unarySubst,InternalOriginalStepGuard.one,sucSubst,zSubst]

theorem markedRename {α β : Type} (x mark depth : OTerm α) (j : α → β) :
    (marked x mark depth).relabel j = marked (x.relabel j) (mark.relabel j) (depth.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (marked x mark depth).subst (fun a => emb (.var (j a))) = _
  rw [markedSubst]
  simp only [← termRelabelAsSubst]

theorem atDepthSubst {α β : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Ty) (depth : OTerm α) (ts : α → OTerm β) :
    (atDepth comp context tau depth).subst (fun a => emb (ts a)) =
      atDepth comp context tau (depth.subst ts) := by
  unfold TypedSpine.atDepth TypedSpine.depthBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [conjunctionSubst,typedSubst,markedSubst,membershipSubst,liftSubst,
    numeralSubst,Term.subst,Sum.elim_inr]

theorem atDepthRename {α β : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Ty) (depth : OTerm α) (j : α → β) :
    (atDepth comp context tau depth).relabel j = atDepth comp context tau (depth.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (atDepth comp context tau depth).subst (fun a => emb (.var (j a))) = _
  rw [atDepthSubst]
  simp only [← termRelabelAsSubst]

theorem depthBodyWitness {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Ty) (depth x mark : OTerm α) :
    (depthBody comp context tau depth).subst
      (Sum.elim Term.var (fun i => emb (![x,mark] i))) =
      (typed comp tau (numeral context) x ⊓ marked x mark depth).imp (membership false x) := by
  have he : (Sum.elim Term.var (fun i => emb (![x,mark] i))) =
      (fun a => emb (Sum.elim Term.var ![x,mark] a)) := by
    funext a
    cases a <;> rfl
  unfold TypedSpine.depthBody
  rw [he,impSubst]
  simp only [conjunctionSubst,typedSubst,markedSubst,membershipSubst,numeralSubst,
    witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem atDepthInstantiate {α : Type} (comp : JointGammaComputability.Data) (context : Nat)
    (tau : Ty) (depth : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (atDepth comp context tau depth) (emb t) =
      atDepth comp context tau (depth.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,atDepthSubst]

theorem atDepthApply {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (context : Nat) (tau : Ty) (depth x mark : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (atDepth comp context tau depth)))
    (ht : Nonempty (Derivation body Gamma (typed comp tau (numeral context) x)))
    (hm : Nonempty (Derivation body Gamma (marked x mark depth))) :
    Nonempty (Derivation body Gamma (membership false x)) := by
  have h := actualFiniteUniversalElimination body α 2 Gamma (depthBody comp context tau depth)
    (fun i => emb (![x,mark] i)) hrow
  rw [depthBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨ht⟩ := ht
  obtain ⟨hm⟩ := hm
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction ht hm)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineSyntaxProof
