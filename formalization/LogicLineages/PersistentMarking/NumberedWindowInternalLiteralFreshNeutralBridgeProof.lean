module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralFactsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalProbeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (membership carrier)
open ID1Completion.InternalFiniteBlocks (block)
open ID1Completion.InternalFiniteBlocksProof (actualFiniteExistentialElimination)
open ID1Completion.SourcePresentation (Data sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalFreshProbeParsedTypedObjectTargets (OpenLiteralParsed literalParsedAt)
open NumberedWindowInternalFreshProbeAlignmentTargets (AlignedCarriersAt)
open NumberedWindowInternalProbeTargets (FreshVariablesComputable typedAt freshAt typeCode)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressReports arrowReports sourceShape)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open ID1Completion.InternalControlGraph (programGraph equal)
open NumberedWindowInternalProbeChecks (exact_TypedComputabilityImpliesMembership)
open NumberedWindowInternalAtomicRefinement (freeSource)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenAtomicRecognition)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalNeutralFactsTargets (D atom Arithmetic FactsAt)
open NumberedWindowInternalNeutralFactsSyntaxProof (atomRename)
open NumberedWindowInternalNeutralFactsProof (exact_ConditionalInternalNeutralFacts)
open NumberedWindowInternalPullbackTargets (ForwardRule)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowComputabilityFormulaTargets (formula)

/-- The actual given fresh probe is accepted by the physical literal
free-variable shape test, at its requested domain and unmodified
packed context. Its original six reported fields remain internal. -/
theorem exact_OpenGivenLiteralFreshVariable (v : Inputs) (W : List ProbeTy)
    (parsed : OpenLiteralParsed v W) (σ τ : Ty) (S : Data) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (q u : OTerm α)
    (typed : D S c Γ (typedAt (chosenH v W) (.arrow σ τ) q))
    (given : D S c Γ (freshAt (chosenA v) q u)) :
    D S c Γ (atom freeSource u) := by
  let B := sourceBody S c
  have opened := parsed σ τ B α Γ q u typed given
  unfold literalParsedAt at opened
  apply actualFiniteExistentialElimination B α 6 Γ _ (atom freeSource u) opened
  let j : α → α ⊕ Fin 6 := Sum.inl
  rw [atomRename]
  let q' := q.relabel j
  let u' := u.relabel j
  let e : Fin 6 → OTerm (α ⊕ Fin 6) := fun k => .var (.inr k)
  let A := addressReports q' (e 0) (e 1) (e 4) ⊓ (arrowReports q' (e 2) (e 3) ⊓
    (sourceShape q' (e 0) (e 1) (e 2) (e 3) (e 4) ⊓ (programGraph v.freshBound (e 5) ![e 4] ⊓
      (equal u' (packedFreeTerm (e 0) (e 2) (e 5)) ⊓
        (equal (e 2) (numeral (typeCode σ)) ⊓ equal (e 3) (numeral (typeCode τ)))))))
  let Δ := A :: Γ.map (fun p => p.relabel j)
  have head : Derivation B Δ A := Derivation.hypothesis List.mem_cons_self
  have inner₁ := Derivation.conjunctionRight head
  have inner₂ := Derivation.conjunctionRight inner₁
  have inner₃ := Derivation.conjunctionRight inner₂
  have inner₄ := Derivation.conjunctionRight inner₃
  have shaped := Derivation.conjunctionLeft inner₄
  obtain ⟨recognized⟩ := exact_OpenAtomicRecognition.1 B _ _ (u.relabel j)
    (.var (.inr 0)) (.var (.inr 2)) (.var (.inr 5)) ⟨shaped⟩
  exact ⟨Derivation.conjunctionLeft recognized⟩

/-- Once the direct neutral arithmetic is supplied, the actual chosen
open typed/fresh inputs meet the fresh computability prerequisite at
every type, not just ground. The carrier and actual variable shape
are both discharged by the already installed literal probes. -/
theorem exact_LiteralFreshFromNeutral (v : Inputs) (W : List ProbeTy)
    (S : Data) (step : Program 3) (neutral bottom : Program 1) (c : Nat)
    (parsed : OpenLiteralParsed v W)
    (aligned : AlignedCarriersAt S v.applicationGuard (chosenH v W) (chosenA v) c)
    (rules : Arithmetic S v.applicationGuard step neutral bottom freeSource c) :
    FreshVariablesComputable S v.applicationGuard (chosenH v W) (chosenA v) c := by
  intro σ τ α Γ q u typed given
  obtain ⟨paid⟩ := aligned σ τ α Γ q u typed given
  have carrierU : D S c Γ (carrier S false c u) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight paid)⟩
  have fresh := exact_OpenGivenLiteralFreshVariable v W parsed σ τ S c α Γ q u typed given
  exact (exact_ConditionalInternalNeutralFacts rules σ).variableCase α Γ u carrierU fresh

/-- At any actual rebuilt original tuple, typed C implies I once
direct neutral arithmetic and positive application forward transport
are supplied. Probe existence, given-fresh alignment, both carriers
and the shape of the actual given variable are no additional premises. -/
theorem exact_TupleComputabilityToIFromArithmetic (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i j : Program 1) (r d : Program 3) (v : Inputs) (c : Nat)
    (step : Program 3) (neutral bottom : Program 1)
    (tuple : TupleAt xs s W i j r d v)
    (rules : Arithmetic (data i j r d) v.applicationGuard step neutral bottom freeSource c)
    (forward : ForwardRule (data i j r d) v.applicationGuard c)
    (τ : Ty) (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    D (data i j r d) c Γ (typedAt (chosenH v W) τ q) →
    D (data i j r d) c Γ (formula v.applicationGuard τ q) →
    D (data i j r d) c Γ (membership false q) := by
  obtain ⟨_,_,_,_,_,guards,_,_,total,shape,aligned⟩ := tuple
  have fresh := exact_LiteralFreshFromNeutral v W (data i j r d) step neutral bottom c
    shape (aligned c) rules
  exact exact_TypedComputabilityImpliesMembership (data i j r d) v.applicationGuard (chosenH v W) (chosenA v) c
    (exact_InternalPullback i j r d v.applicationGuard c guards forward) (total c) fresh τ α Γ q

#print axioms exact_OpenGivenLiteralFreshVariable
#print axioms exact_LiteralFreshFromNeutral
#print axioms exact_TupleComputabilityToIFromArithmetic
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFreshNeutralBridgeProof
