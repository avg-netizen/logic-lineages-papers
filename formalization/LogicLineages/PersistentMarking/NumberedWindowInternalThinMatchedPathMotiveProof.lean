module
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastSubstitutionThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawTickShapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathMotiveProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalComputabilityApplicationSyntaxProof (allEmbeddedSubst liftTermSubst)
open ID1Completion.InternalSourceIntroductionSyntaxProof (formulaRelabelAsSubst termRelabelAsSubst)
open ID1Completion.InternalFiniteBlocksSubstitutionProof (existsSubst)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst liftedEmbedding)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalRecursionGraphSyntaxProof (liftSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (finishAt)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (finishSubst suppliedSubst)
open NumberedWindowInternalSparseLeastSubstitutionThinProof (leastSubst)
open NumberedWindowInternalThinFormationRepresentativeTargets (formation)
open NumberedWindowInternalThinFormationRepresentativeSyntaxProof (formationSubst)
open NumberedWindowInternalSparseApplicationFrontendOpenFormulaProof (auxiliarySubst)
open NumberedWindowInternalSparseRawTickShapeSyntaxProof (rawConsSubst)
open NumberedWindowInternalThinMatchedCallsTargets (pulled)
open NumberedWindowInternalThinMatchedAdvanceTargets (resultOrPath)
open NumberedWindowInternalSparseFieldInductionTargets (atCode atIndex)
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

def clause {α : Type} (ctx dom cod arg cert target value source : OTerm α) : Formula α :=
  let a := auxiliaryTerm dom cod source arg
  let b := auxiliaryTerm dom cod target arg
  (formation W ctx dom cod arg ⊓ (finishAt raw (packedLeastProgram C X W s) ctx (rawCons dom cod) source cert target ⊓
    leastGraph C X W s ctx cod b value)).imp (resultOrPath C X W s raw ctx cod a value)

def safe {α : Type} (ctx dom cod arg cert target value : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  allOne (clause C X W s raw (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
    (cert.relabel j) (target.relabel j) (value.relabel j) (.var (.inr 0)))

private theorem orSubst {α β : Type} (p q : Formula α) (ts : α → Term β) :
    (p ⊔ q).subst ts = p.subst ts ⊔ q.subst ts := rfl

theorem pulledSubst {α β : Type} (ctx cod seed value : OTerm α) (ts : α → OTerm β) :
    (pulled C X W s raw ctx cod seed value).subst (fun a => emb (ts a)) =
    pulled C X W s raw (ctx.subst ts) (cod.subst ts) (seed.subst ts) (value.subst ts) := by
  unfold pulled
  rw [existsSubst,liftedEmbedding,conjunctionSubst,leastSubst,suppliedSubst]
  simp only [liftSubst,Term.subst,Sum.elim_inr]

theorem clauseSubst {α β : Type} (ctx dom cod arg cert target value source : OTerm α) (ts : α → OTerm β) :
    (clause C X W s raw ctx dom cod arg cert target value source).subst (fun a => emb (ts a)) =
    clause C X W s raw (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts)
      (cert.subst ts) (target.subst ts) (value.subst ts) (source.subst ts) := by
  simp only [clause,impSubst,conjunctionSubst,formationSubst,finishSubst,leastSubst,resultOrPath,
    orSubst,pulledSubst,rawConsSubst,auxiliarySubst]

theorem safeSubst {α β : Type} (ctx dom cod arg cert target value : OTerm α) (ts : α → OTerm β) :
    (safe C X W s raw ctx dom cod arg cert target value).subst (fun a => emb (ts a)) =
    safe C X W s raw (ctx.subst ts) (dom.subst ts) (cod.subst ts) (arg.subst ts)
      (cert.subst ts) (target.subst ts) (value.subst ts) := by
  simp only [safe,allEmbeddedSubst,clauseSubst,liftTermSubst]
  rfl

theorem safeRename {α β : Type} (ctx dom cod arg cert target value : OTerm α) (j : α → β) :
    (safe C X W s raw ctx dom cod arg cert target value).relabel j =
    safe C X W s raw (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
      (cert.relabel j) (target.relabel j) (value.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (safe C X W s raw ctx dom cod arg cert target value).subst (fun a => emb (.var (j a))) = _
  rw [safeSubst]
  simp only [termRelabelAsSubst]

def motive {α : Type} (ctx dom cod arg target value : OTerm α) : Formula (α ⊕ Fin 1) :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  safe C X W s raw (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)
    (.var (.inr 0)) (target.relabel j) (value.relabel j)

theorem motiveAt {α : Type} (ctx dom cod arg target value cert : OTerm α) :
    atCode (motive C X W s raw ctx dom cod arg target value) cert =
    safe C X W s raw ctx dom cod arg cert target value := by
  simp only [atCode,motive,instantiate,bindEmbedding,safeSubst,liftBind,varBind]

theorem motiveIndex {α : Type} (ctx dom cod arg target value : OTerm α) (i : Fin 3) :
    atIndex (motive C X W s raw ctx dom cod arg target value) i = safe C X W s raw
      (ctx.relabel Sum.inl) (dom.relabel Sum.inl) (cod.relabel Sum.inl) (arg.relabel Sum.inl) (.var (.inr i))
      (target.relabel Sum.inl) (value.relabel Sum.inl) := by
  unfold atIndex motive
  rw [safeRename]
  simp only [Term.relabel_relabel] <;> rfl

theorem applyAt {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx dom cod arg cert target value source : OTerm α)
    (h : Derivation body Γ (safe C X W s raw ctx dom cod arg cert target value)) :
    Nonempty (Derivation body Γ (clause C X W s raw ctx dom cod arg cert target value source)) := by
  have d := Derivation.universalElimination (emb source) h
  simpa only [instantiate,bindEmbedding,clauseSubst,liftBind,varBind] using Nonempty.intro d


theorem introduce {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (ctx dom cod arg cert target value : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Derivation body Δ (formation W (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j)) →
      Derivation body Δ (finishAt raw (packedLeastProgram C X W s) (ctx.relabel j) ((rawCons dom cod).relabel j)
        x (cert.relabel j) (target.relabel j)) →
      Derivation body Δ (leastGraph C X W s (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) (target.relabel j) (arg.relabel j)) (value.relabel j)) →
      Nonempty (Derivation body Δ (resultOrPath C X W s raw (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) x (arg.relabel j)) (value.relabel j)))) :
    Nonempty (Derivation body Γ (safe C X W s raw ctx dom cod arg cert target value)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := formation W (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) ⊓
    (finishAt raw (packedLeastProgram C X W s) (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) x
      (cert.relabel j) (target.relabel j) ⊓ leastGraph C X W s (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) (target.relabel j) (arg.relabel j)) (value.relabel j))
  let Δ := A :: Γ.map weaken
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have f := Derivation.conjunctionLeft (Derivation.conjunctionRight h)
  obtain ⟨out⟩ := each _ j Δ x (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    (Derivation.conjunctionLeft h) (by rw [NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof.rawConsRename]; exact f)
    (Derivation.conjunctionRight (Derivation.conjunctionRight h))
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction out)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalThinMatchedPathMotiveProof
