module

public import LogicLineages.NativeModule.PersistentMarking.Paper16AccessibilityMilestoneTargetsV2
import LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonProof

/-! Proof of the frozen `Paper16AccessibilityMilestoneTargetsV2.FinishMultisets`
(`lem:arithmetic-accessibility`, multiset checkpoint 3 of
`verification/paper16-remaining-targets-2026-11-25/TARGETS.md`; Fable B, 27 November 2026).

Printed: "Now I-induction on Q gives J({Q}) … Another finite union proves the assertion for
arbitrary accessible member multisets" (ordinals.tex 152–156).

The round-6 derivations `ConditionalJSingletonProof.exact_ConditionalJSingleton` and
`exact_ConditionalJMembers` consume the order-sensitive `MultisetSplit` only to obtain closure of J
under the selected union. Here the same two inductions are run from `UnionClosure` itself, and
`UnionClosure` on the installed presentation is obtained from the certified union step
(`CertifiedMultisetUnion`) through `UnionFeedsCountedReport` on the same union code. -/

public section

namespace LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFinishMultisetsV2
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalSliceInduction
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalJUnionTargets ConditionalJUnionSyntaxProof ConditionalJUnionProof ConditionalJSingletonTargets
open ConditionalJSingletonProof
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open Paper16AccessibilityMilestoneTargetsV2
  (InstalledWindow CertifiedMultisetUnion MultisetGeneration UnionFeedsCountedReport FinishMultisets)

/-- I(q) gives J of the singleton of q, from closure of J under the selected union.
The I-induction and the descendant generation step are those of
`ConditionalJSingletonProof.exact_ConditionalJSingleton`. -/
theorem exact_SingletonFromUnionClosure (d : Data) (c : Nat) (u : Program 2) (sg : Program 1)
    (hUnion : UnionClosure d c u) (hSC : SingletonCarrier d c sg) (hNC : NilCarrier d c)
    (hNS : NilNoStep d c) (hDG : DescendantGeneration d c u sg) :
    SingletonAccessibility d c sg := by
  intro α Γ q s hq hs
  let θ : Formula (α ⊕ Fin 1) := sT sg w
  let H := replacedBody (sliceBody d c false) θ
  have premise : D (sourceBody d c) (H :: Γ.map weaken) θ := by
    have hH : D (sourceBody d c) (H :: Γ.map weaken) (carrier d false c w ⊓ edgeST d c sg w) := by
      rw [← singleShape d c sg]
      exact hyp H
    apply allIntro
    apply intro
    let S := single sg (up w) (w (α := α ⊕ Fin 1))
    have k1 := lift S (andL hH)
    have i1 := lift S (andR hH)
    rw [carrierRelabelG] at k1
    rw [edgeSTRelabel] at i1
    have hK := hSC _ _ (up w) w k1 (hyp S)
    refine ID1Completion.InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction
      d true c _ _ w hK ?_
    apply allIntro
    apply intro
    let E := edge d true c (up w) (w (α := (α ⊕ Fin 1) ⊕ Fin 1))
    have s2 := lift E (hyp (body := sourceBody d c) (Γ := (H :: Γ.map weaken).map weaken) S)
    have i2 := lift E i1
    rw [singleRelabel] at s2
    rw [edgeSTRelabel] at i2
    have nil := nilJ d c hNC hNS (E :: ((S :: (H :: Γ.map weaken).map weaken)).map weaken)
    rw [← membershipInstance] at nil
    have gen := hDG _ _ (membership true w) (up (up w)) (up w) w nil
      (descJ d c sg _ _ i2) (unionClosedJ d c u hUnion _) s2 (hyp E)
    rw [membershipInstance] at gen
    exact gen
  have ind := ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction d c α Γ false θ q premise
  change D _ _ ((membership false q).imp (instantiate (sT sg w) (emb q))) at ind
  rw [sTInstance] at ind
  have h1 := allElim s (mp ind hq)
  rw [sTBodyInstance] at h1
  exact mp h1 hs

/-- Accessible members give J of their multiset, from closure of J under the selected union.
The member generation step is that of `ConditionalJSingletonProof.exact_ConditionalJMembers`. -/
theorem exact_MembersFromUnionClosure (d : Data) (c : Nat) (u mem : Program 2) (sg : Program 1)
    (hUnion : UnionClosure d c u) (hSC : SingletonCarrier d c sg) (hNC : NilCarrier d c)
    (hNS : NilNoStep d c) (hDG : DescendantGeneration d c u sg)
    (hMG : MemberGeneration d c u mem sg) :
    MembersAccessibility d c mem := by
  intro α Γ m h
  have hSing := exact_SingletonFromUnionClosure d c u sg hUnion hSC hNC hNS hDG
  have nil := nilJ d c hNC hNS Γ
  rw [← membershipInstance] at nil
  have members : D (sourceBody d c) Γ (memberSingletons mem sg m (membership true w)) := by
    unfold memberSingletons
    simp only [membershipRelabel]
    apply allIntro
    apply allIntro
    have h' : D (sourceBody d c) Γ (memberIT mem m) := h
    have h2 := liftOnly (liftOnly h')
    rw [memberITRelabel, memberITRelabel] at h2
    apply intro
    apply intro
    let Mb := member mem (.var (.inl (.inr 0)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)) ((m.relabel Sum.inl).relabel Sum.inl)
    let Sg := single sg (.var (.inl (.inr 0)) : OTerm ((α ⊕ Fin 1) ⊕ Fin 1)) (.var (.inr 0))
    have ih := allElim (.var (.inl (.inr 0))) (cons Sg (cons Mb h2))
    rw [memberITBodyInstance] at ih
    have ix := mp ih (cons Sg (hyp Mb))
    exact hSing _ _ _ _ ix (hyp Sg)
  have gen := hMG α Γ (membership true w) m nil members (unionClosedJ d c u hUnion Γ)
  rw [membershipInstance] at gen
  exact gen

variable {S : Spine.Signature} {K : List Ty} {W : List ProbeTy}

/-- On an installed window, the certified union step and the counted report of the selected
union program give closure of J under that union. The two carriers required by the report are
extracted from the two J-memberships. -/
theorem exact_UnionClosureFromCertified (A : InstalledWindow S K W) (c : Nat) (u : Program 2)
    (certified : CertifiedMultisetUnion A c) (report : UnionFeedsCountedReport A c u) :
    UnionClosure A.presentation c u := by
  intro α Γ m n o hm hn hu
  have cm := ID1Completion.InternalAccessibilityRulesProof.actualOriginalCarrierExtraction
    A.presentation true c α Γ m hm
  have cn := ID1Completion.InternalAccessibilityRulesProof.actualOriginalCarrierExtraction
    A.presentation true c α Γ n hn
  exact certified.union certified.split α Γ m n o hm hn (report α Γ m n o cm cn hu)

/-- The frozen multiset checkpoint, for every installed window, context numeral, and
selected union, member and singleton programs. -/
theorem exact_FinishMultisets (A : InstalledWindow S K W) (c : Nat) (u mem : Program 2)
    (sg : Program 1) : FinishMultisets A c u mem sg := by
  intro certified generated
  have closure := exact_UnionClosureFromCertified A c u certified generated.unionReport
  exact ⟨exact_SingletonFromUnionClosure A.presentation c u sg closure generated.singletonCarrier
      generated.nilCarrier generated.nilNoStep generated.descendants,
    exact_MembersFromUnionClosure A.presentation c u mem sg closure generated.singletonCarrier
      generated.nilCarrier generated.nilNoStep generated.descendants generated.members⟩

#print axioms exact_SingletonFromUnionClosure
#print axioms exact_MembersFromUnionClosure
#print axioms exact_UnionClosureFromCertified
#print axioms exact_FinishMultisets

end LogicLineages.PersistentMarking.Paper16AccessibilityMilestoneFinishMultisetsV2
