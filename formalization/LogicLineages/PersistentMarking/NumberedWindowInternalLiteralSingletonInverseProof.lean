module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.InverseApplicationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureLogicProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalSliceInduction (sliceBody)
open ID1Completion.InternalSliceInductionProof (actualInternalSliceInduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm)
open ID1Completion.InternalRecursionClosureLogicProof (closedApply)
open ID1Completion.SourceComputabilityCompletion.InverseApplicationProof (membershipIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode singletonJ)
open NumberedWindowInternalLiteralSingletonStepProof
  (singletonCodeRename exact_OriginalSingletonEdgeLift)
open NumberedWindowInternalLiteralSingletonCarrierReflectionProof
  (D exact_LiteralSingletonCarrierReflection)
open NumberedWindowInternalLiteralSingletonInverseSyntaxProof
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralIToSingletonJ)

/-- The target scalar of every held [even] edge carries its actual carrier.
For arbitrary callbacks r this condition cannot be dropped: one can
deliberately make r accept steps to noncarriers. -/
def ScalarEdgeTargetsCarry (i : Program 1) (r : Program 3) (c : Nat) : Prop :=
  let S := literalData i r
  let B := sourceBody S c
  ∀ (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    D B Γ (edge S false c x y) → D B Γ (carrier S false c y)

private theorem carrierSingletonAfterEquality (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)} (raw x : OTerm α)
    (car : D (sourceBody (literalData i r) c) Γ (carrier (literalData i r) true c raw))
    (eq : D (sourceBody (literalData i r) c) Γ (eqn (singletonCode x) raw)) :
    D (sourceBody (literalData i r) c) Γ (carrier (literalData i r) false c x) := by
  let S := literalData i r
  let B := sourceBody S c
  let d := dCore i r permutation
  have h := (exact_DomainRules i (jRaw i) r d true c B α Γ raw).1 car
  obtain ⟨eq⟩ := eq
  have moved := headTransport (jRaw i) (suc z) raw (singletonCode x) Fin.elim0 ⟨symm eq⟩ h
  have odd := (exact_DomainRules i (jRaw i) r d true c B α Γ (singletonCode x)).2 moved
  exact (exact_LiteralSingletonCarrierReflection i r c α Γ x).1 odd

private theorem progressive (i : Program 1) (r : Program 3) (c : Nat)
    (targetCarrier : ScalarEdgeTargetsCarry i r c)
    {α : Type} {Γ : List (Formula α)} (m : OTerm α)
    (mc : D (sourceBody (literalData i r) c) Γ (carrier (literalData i r) true c m))
    (ml : D (sourceBody (literalData i r) c) Γ (lower (literalData i r) c m)) :
    D (sourceBody (literalData i r) c) Γ (inverse m) := by
  let S := literalData i r
  let B := sourceBody S c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let q : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let m' := m.relabel j
  let A := eqn (singletonCode q) m'
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have eq : D B Δ A := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have odd := renameInto mc j Δ keep
  rw [carrierRename] at odd
  have exactQ := carrierSingletonAfterEquality i r c m' q odd eq
  have lows := renameInto ml j Δ keep
  rw [lowerRename] at lows
  have I : D B Δ (membership false q) := by
    apply membershipIntroduction S c q exactQ
    intro β k Ω y retain strict
    have source := renameInto exactQ k Ω retain
    rw [carrierRename] at source
    have target := targetCarrier β Ω (q.relabel k) y strict
    have singleton := exact_OriginalSingletonEdgeLift i r c β Ω (q.relabel k) y source target strict
    have units := renameInto eq k Ω retain
    change D B Ω ((eqn (singletonCode q) m').relabel k) at units
    rw [eqnRelabel,singletonCodeRename] at units
    have link := edgeFromEquality S c (singletonCode (q.relabel k)) (m'.relabel k)
      (singletonCode y) units singleton
    have lower := renameInto lows k Ω retain
    rw [lowerRename] at lower
    exact inverseAt (singletonCode y) y (lowerAt S c (m'.relabel k) (singletonCode y) lower link) ⟨refl _⟩
  obtain ⟨out⟩ := I
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction out)⟩

/-- Reverse singleton accessibility in the actual internal least
predicate. This is an object J-induction using the original scalar
edge lift, not an external well-foundedness argument. -/
theorem exact_LiteralSingletonJToI (i : Program 1) (r : Program 3) (c : Nat)
    (targetCarrier : ScalarEdgeTargetsCarry i r c)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α)
    (held : D (sourceBody (literalData i r) c) Γ (singletonJ q)) :
    D (sourceBody (literalData i r) c) Γ (membership false q) := by
  let S := literalData i r
  let B := sourceBody S c
  let θ := motive (α := α)
  let m : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let pre := replacedBody (sliceBody S c true) θ
  have step : D B [pre] θ := by
    have hyp : Derivation B [pre] pre := Derivation.hypothesis List.mem_cons_self
    have shape : pre = carrier S true c m ⊓ lower S c m := exact_SingletonInverseSlice S c
    have parts : Derivation B [pre] (carrier S true c m ⊓ lower S c m) :=
      Eq.mp (congrArg (Derivation B [pre]) shape) hyp
    exact progressive i r c targetCarrier m
      ⟨Derivation.conjunctionLeft parts⟩ ⟨Derivation.conjunctionRight parts⟩
  have ind := actualInternalSliceInduction S c α [] true θ (singletonCode q) step
  change D B [] ((singletonJ q).imp (instantiate (motive (α := α)) (emb (singletonCode q)))) at ind
  rw [motiveAt] at ind
  have actual := closedApply ind held
  exact inverseAt (singletonCode q) q actual ⟨refl _⟩

theorem exact_LiteralSingletonMembershipEquivalence (i : Program 1) (r : Program 3) (c : Nat)
    (targetCarrier : ScalarEdgeTargetsCarry i r c)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    let B := sourceBody (literalData i r) c
    D B Γ (singletonJ q) ↔ D B Γ (membership false q) := by
  refine ⟨exact_LiteralSingletonJToI i r c targetCarrier α Γ q,?_⟩
  rintro ⟨given⟩
  obtain ⟨forwards⟩ := exact_LiteralIToSingletonJ i r c α Γ q
  exact ⟨Derivation.implicationElimination forwards given⟩

#print axioms exact_LiteralSingletonJToI
#print axioms exact_LiteralSingletonMembershipEquivalence
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonInverseProof
