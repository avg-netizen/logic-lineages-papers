module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaGroundStepProof
import LogicLineages.PersistentMarking.NumberedWindowTypeApplicationRuleChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaArrowGroundProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.OrdinalComparison.Source (Ty)
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalSourceInversionSupportProof (tagSubstitution)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalTermSubstitutionProof (predicateSubstitution)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts formula)
open NumberedWindowTypeApplicationRuleChecks (exact_ApplicationIntroduction)
open NumberedWindowInternalLiteralRefinedAuxEdgeProof (lambdaAppCode)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof (auxiliaryTermRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open NumberedWindowInternalLiteralLambdaGroundStepProof
  (InstanceAccess ReachesInstance exact_OpenLiteralLambdaGroundStep)

private theorem consRename {α β : Type} (x y : OTerm α) (j : α → β) :
    (consTerm x y).relabel j = consTerm (x.relabel j) (y.relabel j) :=
  rawConsRename x y j

private theorem lambdaAppRename {α β : Type} (j : α → β) (c d t b a : OTerm α) :
    (lambdaAppCode c d t b a).relabel j =
      lambdaAppCode (c.relabel j) (d.relabel j) (t.relabel j) (b.relabel j) (a.relabel j) := by
  simp only [lambdaAppCode,addressTerm,consRename,numeralRename,zRelabel,auxiliaryTermRename,lambdaRename]

private theorem instantiateI {α : Type} (x : OTerm α) :
    instantiate (membership false (.var (.inr (0 : Fin 1)) : OTerm (α ⊕ Fin 1))) (emb x) =
      membership false x := by
  unfold instantiate membership
  rw [bindEmbedding,← predicateSubstitution,tagSubstitution,varBind]

private theorem moveI {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} (x y : OTerm α)
    (eq : Nonempty (Derivation B Γ (equal y x)))
    (hx : Nonempty (Derivation B Γ (membership false x))) :
    Nonempty (Derivation B Γ (membership false y)) := by
  obtain ⟨e⟩ := eq
  rw [equalEqn] at e
  obtain ⟨h⟩ := hx
  let G : Formula (α ⊕ Fin 1) := membership false (.var (.inr 0))
  have atX : Derivation B Γ (instantiate G (emb x)) := by
    rw [show instantiate G (emb x) = membership false x from instantiateI x]
    exact h
  have atY := Derivation.equalityElimination G (emb x) (emb y) (symm e) atX
  rw [show instantiate G (emb y) = membership false y from instantiateI y] at atY
  exact ⟨atY⟩

/-- Landing must concern the original accepted application and retain
the precise representative argument and the computation's own target.
This premise is not supplied by numeral calibration. -/
@[expose] def LambdaApplicationLanding (S : Data) (n : Nat) (p : Program 3) (σ : Ty)
    {α : Type} (Γ : List (Formula α)) (ctx dom arrowTy cod rawBody : OTerm α) : Prop :=
  ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (u y : OTerm β),
    (∀ f ∈ Γ, f.relabel j ∈ Δ) →
    Nonempty (Derivation (sourceBody S n) Δ
      (accepts p ((addressTerm ctx arrowTy (lambdaTerm dom rawBody)).relabel j) u y)) →
    Nonempty (Derivation (sourceBody S n) Δ (formula p σ u)) →
    ∃ arg : OTerm β,
      Nonempty (Derivation (sourceBody S n) Δ
        (equal y (lambdaAppCode (ctx.relabel j) (dom.relabel j) (cod.relabel j) (rawBody.relabel j) arg))) ∧
      Nonempty (Derivation (sourceBody S n) Δ
        (carrier S false n
          (lambdaAppCode (ctx.relabel j) (dom.relabel j) (cod.relabel j) (rawBody.relabel j) arg)))

/-- Conditional actual C at a literal lambda of ground codomain. The
original object arrow introduction introduces both argument and result.
Its premise consumes the actual P acceptance and domain C, then the
ground-step proof discharges the selected lambda application. -/
theorem exact_OpenLiteralLambdaArrowGroundC (S : Data) (n : Nat) (p : Program 3)
    (guard argSlot bodySlot sub : Program 2) (least : Program 3) (σ : Ty)
    {α : Type} {Γ : List (Formula α)} (ctx dom arrowTy cod rawBody : OTerm α)
    (landing : LambdaApplicationLanding S n p σ Γ ctx dom arrowTy cod rawBody)
    (paid : InstanceAccess S n sub least)
    (cover : ∀ (β : Type) (Δ : List (Formula β)) (c d t b a y : OTerm β),
      Nonempty (Derivation (sourceBody S n) Δ (edge S false n (lambdaAppCode c d t b a) y)) →
      ReachesInstance (sourceBody S n) Δ guard argSlot bodySlot sub least c d t b a y ∨
      Nonempty (Derivation (sourceBody S n) Δ (membership false y))) :
    Nonempty (Derivation (sourceBody S n) Γ
      (formula p (.arrow σ .ground) (addressTerm ctx arrowTy (lambdaTerm dom rawBody)))) := by
  let f := addressTerm ctx arrowTy (lambdaTerm dom rawBody)
  let B := sourceBody S n
  apply exact_ApplicationIntroduction B p σ .ground α Γ f
  let β := (α ⊕ Fin 1) ⊕ Fin 1
  let j : α → β := fun x => .inl (.inl x)
  let u : OTerm β := .var (.inl (.inr 0))
  let y : OTerm β := .var (.inr 0)
  let A := formula p σ u
  let H := accepts p (f.relabel j) u y
  let Δ := A :: H :: (Γ.map weaken).map weaken
  change Nonempty (Derivation B Δ (membership false y))
  have keep : ∀ g ∈ Γ, g.relabel j ∈ Δ := by
    intro g hg
    apply List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    refine List.mem_map.mpr ⟨g.relabel Sum.inl,List.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
    exact formulaRelabelComposition (Sum.inl : α → α ⊕ Fin 1) (Sum.inl : α ⊕ Fin 1 → β) g
  obtain ⟨arg,same,carried⟩ := landing β j Δ u y keep
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  apply moveI (lambdaAppCode (ctx.relabel j) (dom.relabel j) (cod.relabel j) (rawBody.relabel j) arg) y same
  apply exact_OpenLiteralLambdaGroundStep S n p guard argSlot bodySlot sub least
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (rawBody.relabel j) arg carried paid
  intro γ k Θ target _ happened
  rw [lambdaAppRename] at happened
  exact cover γ Θ _ _ _ _ _ target happened

#print axioms exact_OpenLiteralLambdaArrowGroundC
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaArrowGroundProof
