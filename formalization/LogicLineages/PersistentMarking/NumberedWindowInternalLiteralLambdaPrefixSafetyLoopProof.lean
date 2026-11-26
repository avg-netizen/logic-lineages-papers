module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyTickProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyLoopProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (allOne)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalControlGraphSupportProof (valueUnique emptyRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBinderTransportProof (actualUniversalRenaming)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding nextEmbedding liftBind varBind zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (impSubst liftNext varNext)
open ID1Completion.InternalNumericIteration (repeatGraph repeatProgram)
open ID1Completion.InternalNumericIterationSupportProof (repeatZeroValue repeatSuccRecover)
open ID1Completion.InternalNumericIterationSyntaxProof (repeatRename repeatSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof (prefixTick)
open NumberedWindowInternalLiteralLambdaPrefixSafetySyntaxProof
open NumberedWindowInternalLiteralLambdaPrefixSafetyTickProof (exact_OpenPrefixTickSafe)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def loopBody {α : Type} (W : Program 3) (fuel before out : OTerm α) : Formula α :=
  (repeatGraph (prefixTick W) out fuel before).imp (prefixSafe out)

private def loopMotive {α : Type} (W : Program 3) (fuel before : OTerm α) : Formula α :=
  allOne (loopBody W (fuel.relabel Sum.inl) (before.relabel Sum.inl) (.var (.inr 0)))

private theorem loopBodyRename {β : Type} (W : Program 3) (fuel before out : OTerm α) (j : α → β) :
    (loopBody W fuel before out).relabel j =
      loopBody W (fuel.relabel j) (before.relabel j) (out.relabel j) := by
  change ((repeatGraph (prefixTick W) out fuel before).relabel j).imp ((prefixSafe out).relabel j) = _
  rw [repeatRename,prefixSafeRename]
  rfl

private theorem loopBodySubst {β : Type} (W : Program 3) (fuel before out : OTerm α) (ts : α → OTerm β) :
    (loopBody W fuel before out).subst (fun a => emb (ts a)) =
      loopBody W (fuel.subst ts) (before.subst ts) (out.subst ts) := by
  simp only [loopBody,impSubst,repeatSubst,prefixSafeSubst]

private theorem loopMotiveRename {β : Type} (W : Program 3) (fuel before : OTerm α) (j : α → β) :
    (loopMotive W fuel before).relabel j =
      loopMotive W (fuel.relabel j) (before.relabel j) := by
  unfold loopMotive
  rw [actualUniversalRenaming,loopBodyRename]
  simp only [Term.relabel_relabel]
  rfl

private theorem loopMotiveSubst {β : Type} (W : Program 3) (fuel before : OTerm α) (ts : α → OTerm β) :
    (loopMotive W fuel before).subst (fun a => emb (ts a)) =
      loopMotive W (fuel.subst ts) (before.subst ts) := by
  unfold loopMotive
  rw [allEmbeddedSubst,loopBodySubst,liftTermSubst,liftTermSubst]
  rfl

private theorem loopMotiveIntro (W : Program 3) (fuel before : OTerm α)
    (go : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (out : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      D B Δ (repeatGraph (prefixTick W) out (fuel.relabel j) (before.relabel j)) →
      D B Δ (prefixSafe out)) : D B Γ (loopMotive W fuel before) := by
  let out : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let P := repeatGraph (prefixTick W) out (fuel.relabel Sum.inl) (before.relabel Sum.inl)
  obtain ⟨d⟩ := go (α ⊕ Fin 1) Sum.inl (P :: Γ.map weaken) out
    (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction d)⟩

private theorem loopMotiveApply (W : Program 3) (fuel before out : OTerm α)
    (m : D B Γ (loopMotive W fuel before))
    (run : D B Γ (repeatGraph (prefixTick W) out fuel before)) : D B Γ (prefixSafe out) := by
  obtain ⟨d⟩ := m
  obtain ⟨r⟩ := run
  let P : Formula (α ⊕ Fin 1) := loopBody W (fuel.relabel Sum.inl) (before.relabel Sum.inl) (.var (.inr 0))
  have ul : Derivation B Γ (allOne P) := d
  have inst : instantiate P (emb out) = loopBody W fuel before out := by
    simp only [P,instantiate,bindEmbedding,loopBodySubst,liftBind,varBind]
  have h := Derivation.universalElimination (emb out) ul
  rw [inst] at h
  exact ⟨Derivation.implicationElimination h r⟩

private theorem zeroMotive (W : Program 3) (before : OTerm α) (safe : D B Γ (prefixSafe before)) :
    D B Γ (loopMotive W z before) := by
  apply loopMotiveIntro W z before
  intro β j Δ out keep held
  rw [zRelabel] at held
  let p := prefixTick W
  let b := before.relabel j
  have initial := renameInto safe j Δ keep
  rw [prefixSafeRename] at initial
  have exactZero := repeatZeroValue (body := B) (Gamma := Δ) p b
  have eq := valueUnique (repeatProgram p) b out (Fin.cons z (Fin.cons b Fin.elim0)) exactZero held
  exact prefixSafeMove b out initial eq

private theorem nextMotive (W : Program 3) (fuel before : OTerm α)
    (ih : D B Γ (loopMotive W fuel before)) : D B Γ (loopMotive W (suc fuel) before) := by
  apply loopMotiveIntro W (suc fuel) before
  intro β j Δ out keep held
  rw [sucRelabel] at held
  let p := prefixTick W
  let f := fuel.relabel j
  let a := before.relabel j
  apply programCases (repeatProgram p) (Fin.cons f (Fin.cons a Fin.elim0)) _
  intro γ k Ω prev stay prior
  rw [prefixSafeRename]
  simp only [consTermRename,emptyRename] at prior
  have run := renameInto held k Ω stay
  rw [repeatRename,sucRelabel] at run
  have v := renameInto ih j Δ keep
  rw [loopMotiveRename] at v
  have h := renameInto v k Ω stay
  rw [loopMotiveRename] at h
  have safe := loopMotiveApply W (f.relabel k) (a.relabel k) prev h prior
  have tick := repeatSuccRecover p (f.relabel k) prev (out.relabel k) (a.relabel k) prior run
  exact exact_OpenPrefixTickSafe W prev (out.relabel k) safe tick

/-- Rejection is the only reachable non-unit flag. This is an
arithmetic induction on the actual primitive recursion graph. -/
theorem exact_OpenPrefixLoopSafe (W : Program 3) (fuel before out : OTerm α)
    (safe : D B Γ (prefixSafe before))
    (run : D B Γ (repeatGraph (prefixTick W) out fuel before)) : D B Γ (prefixSafe out) := by
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let j : α → α ⊕ Fin 1 := Sum.inl
  let theta : Formula (α ⊕ Fin 1) := loopMotive W v (before.relabel j)
  have inst (x : OTerm α) : instantiate theta (emb x) = loopMotive W x before := by
    simp only [theta,instantiate,bindEmbedding,loopMotiveSubst,j,v,liftBind,varBind]
  have step : successorInstance theta = loopMotive W (suc v) (before.relabel j) := by
    simp only [theta,successorInstance,nextEmbedding,loopMotiveSubst,j,v,liftNext,varNext]
  obtain ⟨base⟩ := zeroMotive W before safe
  obtain ⟨next⟩ := nextMotive (Γ := theta :: Γ.map weaken) W v (before.relabel j)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have inductionResult := Derivation.universalElimination (emb fuel)
    (natInduction theta (by rw [inst]; exact base) (by rw [step]; exact next))
  rw [inst] at inductionResult
  exact loopMotiveApply W fuel before out ⟨inductionResult⟩ run

#print axioms exact_OpenPrefixLoopSafe
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixSafetyLoopProof
