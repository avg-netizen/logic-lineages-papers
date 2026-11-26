module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJSingletonTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionProof

/-! Proof of the frozen `ConditionalJSingletonTargets` (sha256 cec67446…b867): I-induction (the
scalar slice of the accepted ID₁ induction) gives J of singletons; the descendant generation
schema, instantiated at the J-predicate, carries the finite union through #1487
(`exact_ConditionalJUnion`); the member generation schema gives J of multisets with accessible
members. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJSingletonProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalSliceInduction
open ID1Completion.InternalAccessibilityRulesSyntaxProof (membershipSubst edgeSubst)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb bindEmbedding liftBind varBind)
open ConditionalUpperUniformInstanceProof (carrierSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalJUnionTargets ConditionalJUnionSyntaxProof ConditionalJUnionProof ConditionalJSingletonTargets

/-! Templates. -/

/-- ∀ s (single q s → J s). -/
def sT {α : Type} (sg : Program 1) (q : OTerm α) : Formula α :=
  allOne ((single sg (up q) w).imp (membership true w))

/-- ∀ q' (edge q q' → sT q'): the I-induction hypothesis. -/
def edgeST {α : Type} (d : Data) (c : Nat) (sg : Program 1) (q : OTerm α) : Formula α :=
  allOne ((edge d false c (up q) w).imp (sT sg w))

/-- ∀ x (member x m → I x). -/
def memberIT {α : Type} (mem : Program 2) (m : OTerm α) : Formula α :=
  allOne ((member mem w (up m)).imp (membership false w))

/-! Substitution, renaming, instances. -/

theorem membershipRelabelG {α β : Type} (odd : Bool) (x : OTerm α) (f : α → β) :
    (membership odd x).relabel f = membership odd (x.relabel f) := by
  rw [relabelEmb, membershipSubst, termRelabel]

theorem carrierRelabelG {α β : Type} (d : Data) (odd : Bool) (c : Nat) (x : OTerm α) (f : α → β) :
    (carrier d odd c x).relabel f = carrier d odd c (x.relabel f) := by
  rw [relabelEmb, carrierSubst, termRelabel]

theorem singleSubst {α β : Type} (sg : Program 1) (q s : OTerm α) (ts : α → OTerm β) :
    (single sg q s).subst (fun a => emb (ts a)) = single sg (q.subst ts) (s.subst ts) := by
  unfold single
  rw [graphSubst]
  congr 1
  funext i
  exact Fin.cases rfl (fun k => Fin.elim0 k) i

theorem memberSubst {α β : Type} (mem : Program 2) (x m : OTerm α) (ts : α → OTerm β) :
    (member mem x m).subst (fun a => emb (ts a)) = member mem (x.subst ts) (m.subst ts) := by
  unfold member
  rw [graphSubst]
  congr 1
  · exact ID1Completion.InternalAccessibilityRulesSyntaxProof.numeralSubst 1 ts
  · funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem singleRelabel {α β : Type} (sg : Program 1) (q s : OTerm α) (f : α → β) :
    (single sg q s).relabel f = single sg (q.relabel f) (s.relabel f) := by
  rw [relabelEmb, singleSubst, termRelabel, termRelabel]

theorem sTSubst {α β : Type} (sg : Program 1) (q : OTerm α) (ts : α → OTerm β) :
    (sT sg q).subst (fun a => emb (ts a)) = sT sg (q.subst ts) := by
  unfold sT
  rw [allOneSubst, ID1Completion.InternalRecursionClosureSyntaxProof.liftedEmbedding]
  change allOne (((single sg (up q) w).subst _).imp ((membership true w).subst _)) = _
  rw [singleSubst, membershipSubst, ID1Completion.InternalRecursionGraphSyntaxProof.liftSubst]
  rfl

theorem edgeSTSubst {α β : Type} (d : Data) (c : Nat) (sg : Program 1) (q : OTerm α) (ts : α → OTerm β) :
    (edgeST d c sg q).subst (fun a => emb (ts a)) = edgeST d c sg (q.subst ts) := by
  unfold edgeST
  rw [allOneSubst, ID1Completion.InternalRecursionClosureSyntaxProof.liftedEmbedding]
  change allOne (((edge d false c (up q) w).subst _).imp ((sT sg w).subst _)) = _
  rw [edgeSubst, sTSubst, ID1Completion.InternalRecursionGraphSyntaxProof.liftSubst]
  rfl

theorem memberITSubst {α β : Type} (mem : Program 2) (m : OTerm α) (ts : α → OTerm β) :
    (memberIT mem m).subst (fun a => emb (ts a)) = memberIT mem (m.subst ts) := by
  unfold memberIT
  rw [allOneSubst, ID1Completion.InternalRecursionClosureSyntaxProof.liftedEmbedding]
  change allOne (((member mem w (up m)).subst _).imp ((membership false w).subst _)) = _
  rw [memberSubst, membershipSubst, ID1Completion.InternalRecursionGraphSyntaxProof.liftSubst]
  rfl

theorem sTRelabel {α β : Type} (sg : Program 1) (q : OTerm α) (f : α → β) :
    (sT sg q).relabel f = sT sg (q.relabel f) := by
  rw [relabelEmb, sTSubst, termRelabel]

theorem edgeSTRelabel {α β : Type} (d : Data) (c : Nat) (sg : Program 1) (q : OTerm α) (f : α → β) :
    (edgeST d c sg q).relabel f = edgeST d c sg (q.relabel f) := by
  rw [relabelEmb, edgeSTSubst, termRelabel]

theorem memberITRelabel {α β : Type} (mem : Program 2) (m : OTerm α) (f : α → β) :
    (memberIT mem m).relabel f = memberIT mem (m.relabel f) := by
  rw [relabelEmb, memberITSubst, termRelabel]

theorem sTInstance {α : Type} (sg : Program 1) (t : OTerm α) :
    instantiate (sT sg (w (α := α))) (emb t) = sT sg t := by
  unfold instantiate
  rw [bindEmbedding, sTSubst, varBind]

theorem sTBodyInstance {α : Type} (sg : Program 1) (q t : OTerm α) :
    instantiate ((single sg (up q) w).imp (membership true w)) (emb t) =
      (single sg q t).imp (membership true t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((single sg (up q) w).subst _).imp ((membership true w).subst _) = _
  rw [singleSubst, membershipSubst, liftBind, varBind]

theorem edgeSTBodyInstance {α : Type} (d : Data) (c : Nat) (sg : Program 1) (q t : OTerm α) :
    instantiate ((edge d false c (up q) w).imp (sT sg w)) (emb t) =
      (edge d false c q t).imp (sT sg t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((edge d false c (up q) w).subst _).imp ((sT sg w).subst _) = _
  rw [edgeSubst, sTSubst, liftBind, varBind]

theorem memberITBodyInstance {α : Type} (mem : Program 2) (m t : OTerm α) :
    instantiate ((member mem w (up m)).imp (membership false w)) (emb t) =
      (member mem t m).imp (membership false t) := by
  unfold instantiate
  rw [bindEmbedding]
  change ((member mem w (up m)).subst _).imp ((membership false w).subst _) = _
  rw [memberSubst, membershipSubst, liftBind, varBind]

theorem singleShape {α : Type} (d : Data) (c : Nat) (sg : Program 1) :
    replacedBody (sliceBody d c false) (sT sg (w (α := α))) =
      carrier d false c (w (α := α)) ⊓ edgeST d c sg (w (α := α)) := by
  rw [ID1Completion.InternalSliceInductionSyntaxProof.sliceReplacement]
  unfold PositiveArithmeticPredicateSubstitution.liftPredicateFormula
  rw [sTRelabel]
  rfl

/-! Derivations. -/

theorem liftOnly {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)} {φ : Formula α}
    (h : D body Γ φ) : D body (Γ.map weaken) (φ.relabel Sum.inl) :=
  ID1Completion.InternalDerivationRenamingProof.actualDerivationRenaming body α (α ⊕ Fin 1) Sum.inl Γ φ h

theorem nilJ (d : Data) (c : Nat) (hNC : NilCarrier d c) (hNS : NilNoStep d c) {α : Type}
    (Γ : List (Formula α)) :
    D (sourceBody d c) Γ (membership true (OrdinaryArithmetic.zeroTerm : OTerm α)) := by
  refine ID1Completion.InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction
    d true c α Γ _ (hNC α Γ) ?_
  apply allIntro
  apply intro
  have hz : (OrdinaryArithmetic.zeroTerm : OTerm α).relabel (Sum.inl : α → α ⊕ Fin 1) =
      OrdinaryArithmetic.zeroTerm := ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel _
  have e : D (sourceBody d c)
      (edge d true c ((OrdinaryArithmetic.zeroTerm : OTerm α).relabel Sum.inl) (w (α := α)) :: Γ.map weaken)
      (edge d true c OrdinaryArithmetic.zeroTerm (w (α := α))) := by
    rw [← hz]
    exact hyp _
  obtain ⟨b⟩ := hNS _ _ _ e
  exact ⟨Derivation.explosion b⟩

theorem unionClosedJ (d : Data) (c : Nat) (u : Program 2) (hU : UnionClosure d c u) {α : Type}
    (Γ : List (Formula α)) :
    D (sourceBody d c) Γ (unionClosed u (membership true (w (α := α)))) := by
  unfold unionClosed
  simp only [membershipRelabel]
  apply allIntro
  apply allIntro
  apply allIntro
  apply intro
  apply intro
  apply intro
  exact hU _ _ _ _ _ (cons _ (cons _ (hyp _))) (cons _ (hyp _)) (hyp _)

theorem descJ (d : Data) (c : Nat) (sg : Program 1) {γ : Type} (Θ : List (Formula γ)) (q : OTerm γ)
    (h : D (sourceBody d c) Θ (edgeST d c sg q)) :
    D (sourceBody d c) Θ (descendantSingletons d c sg q (membership true (w (α := γ)))) := by
  unfold descendantSingletons
  simp only [membershipRelabel]
  apply allIntro
  apply allIntro
  have h2 := liftOnly (liftOnly h)
  rw [edgeSTRelabel, edgeSTRelabel] at h2
  apply intro
  apply intro
  let Ed := edge d false c ((q.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr 0)) : OTerm ((γ ⊕ Fin 1) ⊕ Fin 1))
  let Sg := single sg (.var (.inl (.inr 0)) : OTerm ((γ ⊕ Fin 1) ⊕ Fin 1)) (.var (.inr 0))
  have ih := allElim (.var (.inl (.inr 0))) (cons Sg (cons Ed h2))
  rw [edgeSTBodyInstance] at ih
  have st := mp ih (cons Sg (hyp Ed))
  have atT := allElim (.var (.inr 0)) st
  rw [sTBodyInstance] at atT
  exact mp atT (hyp Sg)

theorem exact_ConditionalJSingleton : ConditionalJSingleton := by
  intro d c u sg hCU hMS hSC hNC hNS hDG α Γ q s hq hs
  have hUnion : UnionClosure d c u := ConditionalJUnionProof.exact_ConditionalJUnion d c u hCU hMS
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

theorem exact_ConditionalJMembers : ConditionalJMembers := by
  intro d c u mem sg hCU hMS hSC hNC hNS hDG hMG α Γ m h
  have hUnion : UnionClosure d c u := ConditionalJUnionProof.exact_ConditionalJUnion d c u hCU hMS
  have hSing := exact_ConditionalJSingleton d c u sg hCU hMS hSC hNC hNS hDG
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

#print axioms exact_ConditionalJSingleton
#print axioms exact_ConditionalJMembers

end LogicLineages.PersistentMarking.ConditionalJSingletonProof
