module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof


@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountEffectProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalAdditionLawsProof (impSubst addSubst)
open SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open NumberedWindowInternalLiteralCount (entryCount)
open NumberedWindowInternalLiteralScratchEraseCountTransportProof (delta)

def matrix {alpha : Type} (raw needle rest bit : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  (graph2 entryCount (x 1) (raw.relabel j) (x 0) ⊓
    graph2 entryCount (x 2) (rest.relabel j) (x 0)).imp
    (delta (needle.relabel j) (x 0) (x 1) (x 2) (bit.relabel j))

/-- For all actual queries, with their actual literal count values. -/
def countEffect {alpha : Type} (raw needle rest bit : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix raw needle rest bit)

private theorem deltaSubst {alpha beta : Type} (needle query lc rc bit : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (delta needle query lc rc bit).subst (fun a => emb (ts a)) =
      delta (needle.subst ts) (query.subst ts) (lc.subst ts) (rc.subst ts) (bit.subst ts) := by
  unfold delta
  simp only [impSubst,conjunctionSubst,notSubst,eqnSubst,addSubst]

theorem countEffectSubst {alpha beta : Type} (raw needle rest bit : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (countEffect raw needle rest bit).subst (fun a => emb (ts a)) =
      countEffect (raw.subst ts) (needle.subst ts) (rest.subst ts) (bit.subst ts) := by
  unfold countEffect matrix
  rw [allBlockSubst,liftedEmbedding]
  simp only [impSubst,conjunctionSubst,graph2,programSubst,deltaSubst,
    consTermSubst,emptySubst,InternalRecursionGraphSyntaxProof.liftSubst,Term.subst,Sum.elim_inr]

theorem countEffectRename {alpha beta : Type} (raw needle rest bit : OTerm alpha) (j : alpha → beta) :
    (countEffect raw needle rest bit).relabel j =
      countEffect (raw.relabel j) (needle.relabel j) (rest.relabel j) (bit.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (countEffect raw needle rest bit).subst (fun a => emb (.var (j a))) = _
  rw [countEffectSubst]
  simp only [← termRelabelAsSubst]

private theorem graph2Subst {alpha beta : Type} (out raw needle : OTerm alpha) (ts : alpha → OTerm beta) :
    (graph2 entryCount out raw needle).subst (fun a => emb (ts a)) =
      graph2 entryCount (out.subst ts) (raw.subst ts) (needle.subst ts) := by
  unfold graph2
  simp only [programSubst,consTermSubst,emptySubst]

theorem matrixWitness {alpha : Type} (raw needle rest bit query lc rc : OTerm alpha) :
    (matrix raw needle rest bit).subst (Sum.elim Term.var (fun i => emb (![query,lc,rc] i))) =
      (graph2 entryCount lc raw query ⊓ graph2 entryCount rc rest query).imp (delta needle query lc rc bit) := by
  let tape : Fin 3 → OTerm alpha := ![query,lc,rc]
  let terms : alpha ⊕ Fin 3 → OTerm alpha := Sum.elim Term.var tape
  have he : (Sum.elim Term.var (fun i => emb (tape i))) = (fun a => emb (terms a)) := by
    funext a
    cases a <;> rfl
  have keep (x : OTerm alpha) : (x.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)).subst terms = x :=
    InternalRecursionGraphSyntaxProof.witnessLift x tape
  have h0 : (Term.var (.inr (0 : Fin 3)) : OTerm (alpha ⊕ Fin 3)).subst terms = query := rfl
  have h1 : (Term.var (.inr (1 : Fin 3)) : OTerm (alpha ⊕ Fin 3)).subst terms = lc := rfl
  have h2 : (Term.var (.inr (2 : Fin 3)) : OTerm (alpha ⊕ Fin 3)).subst terms = rc := rfl
  change (matrix raw needle rest bit).subst (Sum.elim Term.var (fun i => emb (tape i))) = _
  rw [he]
  unfold matrix
  simp only [impSubst,conjunctionSubst,graph2Subst,deltaSubst,keep,h0,h1,h2]

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applyAt (raw needle rest bit query lc rc : OTerm alpha)
    (h : Nonempty (Derivation body Delta (countEffect raw needle rest bit)))
    (hl : Nonempty (Derivation body Delta (graph2 entryCount lc raw query)))
    (hr : Nonempty (Derivation body Delta (graph2 entryCount rc rest query))) :
    Nonempty (Derivation body Delta (delta needle query lc rc bit)) := by
  unfold countEffect at h
  obtain ⟨d⟩ := InternalClosedProgramsBindingProof.elimination body alpha 3 Delta _
    (fun i => emb (![query,lc,rc] i)) h
  rw [matrixWitness] at d
  obtain ⟨hf⟩ := andIntro hl hr
  exact ⟨Derivation.implicationElimination d hf⟩

theorem introduce (raw needle rest bit : OTerm alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (query lc rc : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 entryCount lc (raw.relabel j) query)) →
      Nonempty (Derivation body Theta (graph2 entryCount rc (rest.relabel j) query)) →
      Nonempty (Derivation body Theta (delta (needle.relabel j) query lc rc (bit.relabel j)))) :
    Nonempty (Derivation body Delta (countEffect raw needle rest bit)) := by
  unfold countEffect
  apply InternalClosedProgramsBindingProof.introduction body alpha 3 Delta
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let f := graph2 entryCount (x 1) (raw.relabel Sum.inl) (x 0) ⊓
    graph2 entryCount (x 2) (rest.relabel Sum.inl) (x 0)
  let Theta : List (Formula (alpha ⊕ Fin 3)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  obtain ⟨d⟩ := next (alpha ⊕ Fin 3) Sum.inl Theta (x 0) (x 1) (x 2) hi (andLeft hf) (andRight hf)
  exact ⟨Derivation.implicationIntroduction d⟩
#print axioms applyAt
#print axioms introduce
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseCountEffectProof
