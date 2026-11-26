module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalJUnionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSliceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

/-! Proof of the frozen `ConditionalJUnionTargets.ConditionalJUnion` (sha256 a5474b2b…4f48): the printed
nested induction — outer J-induction on one component, inner J-induction on the other — inside the
ID₁ calculus, using the accepted slice induction (`actualInternalSliceInduction`, `sliceReplacement`),
the accepted accessibility introduction rule, ∃/⊥/equality rules of the calculus, and the two
arithmetic premises `CarrierUnion`, `MultisetSplit`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalJUnionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules ID1Completion.SourcePresentation
open ID1Completion.InternalSliceInduction
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm emb eqn bindEmbedding liftBind varBind)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ConditionalJUnionTargets ConditionalJUnionSyntaxProof

section Logic
variable {body : Positive (Fin 1)}

abbrev D {α : Type} (body : Positive (Fin 1)) (Γ : List (Formula α)) (φ : Formula α) : Prop :=
  Nonempty (Derivation body Γ φ)

theorem cons {α : Type} {Γ : List (Formula α)} {φ : Formula α} (ψ : Formula α) (h : D body Γ φ) :
    D body (ψ :: Γ) φ := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.weakening (fun p hp => List.mem_cons_of_mem _ hp) h⟩

theorem hyp {α : Type} {Γ : List (Formula α)} (φ : Formula α) : D body (φ :: Γ) φ :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem mp {α : Type} {Γ : List (Formula α)} {φ ψ : Formula α}
    (h : D body Γ (φ.imp ψ)) (a : D body Γ φ) : D body Γ ψ := by
  obtain ⟨h⟩ := h
  obtain ⟨a⟩ := a
  exact ⟨Derivation.implicationElimination h a⟩

theorem intro {α : Type} {Γ : List (Formula α)} {φ ψ : Formula α}
    (h : D body (φ :: Γ) ψ) : D body Γ (φ.imp ψ) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem andL {α : Type} {Γ : List (Formula α)} {φ ψ : Formula α} (h : D body Γ (φ ⊓ ψ)) : D body Γ φ := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionLeft h⟩

theorem andR {α : Type} {Γ : List (Formula α)} {φ ψ : Formula α} (h : D body Γ (φ ⊓ ψ)) : D body Γ ψ := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionRight h⟩

theorem andI {α : Type} {Γ : List (Formula α)} {φ ψ : Formula α}
    (a : D body Γ φ) (b : D body Γ ψ) : D body Γ (φ ⊓ ψ) := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  exact ⟨Derivation.conjunctionIntroduction a b⟩

theorem byCases {α : Type} {Γ : List (Formula α)} (A C : Formula α)
    (pos : D body (A :: Γ) C) (neg : D body (A.not :: Γ) C) : D body Γ C := by
  have hp : D body Γ (A.imp C) := intro pos
  have hn : D body Γ (A.not.imp C) := intro neg
  have notA : D body (C.not :: Γ) A.not := by
    have e : D body (A :: C.not :: Γ) C := mp (cons _ (cons _ hp)) (hyp A)
    have f : D body (A :: C.not :: Γ) (C.imp ⊥) := cons A (hyp C.not)
    exact intro (mp f e)
  have c : D body (C.not :: Γ) C := mp (cons _ hn) notA
  have bot : D body (C.not :: Γ) ⊥ := mp (hyp (Γ := Γ) C.not) c
  obtain ⟨bot⟩ := bot
  exact ⟨Derivation.classical bot⟩

theorem lift {α : Type} {Γ : List (Formula α)} {φ : Formula α} (ψ : Formula (α ⊕ Fin 1))
    (h : D body Γ φ) : D body (ψ :: Γ.map weaken) (φ.relabel Sum.inl) :=
  cons ψ (ID1Completion.InternalDerivationRenamingProof.actualDerivationRenaming body α (α ⊕ Fin 1)
    Sum.inl Γ φ h)

theorem allIntro {α : Type} {Γ : List (Formula α)} {φ : Formula (α ⊕ Fin 1)}
    (h : D body (Γ.map weaken) φ) : D body Γ (allOne φ) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.universalIntroduction h⟩

theorem allElim {α : Type} {Γ : List (Formula α)} {φ : Formula (α ⊕ Fin 1)} (t : OTerm α)
    (h : D body Γ (allOne φ)) : D body Γ (instantiate φ (emb t)) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.universalElimination (emb t) h⟩

theorem existsElim {α : Type} {Γ : List (Formula α)} {φ : Formula (α ⊕ Fin 1)} {ψ : Formula α}
    (h : D body Γ (existsOne φ)) (k : D body (φ :: Γ.map weaken) (weaken ψ)) : D body Γ ψ := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  exact ⟨Derivation.existentialElimination h k⟩

/-- Rewrite `m' = m`, as an equation, inside the first slot of the union graph. -/
theorem unionRewrite {α : Type} {Γ : List (Formula α)} (u : Program 2) {s t n o : OTerm α}
    (e : D body Γ (eqn s t)) (h : D body Γ (union u s n o)) : D body Γ (union u t n o) := by
  obtain ⟨e⟩ := e
  have h' : D body Γ (instantiate (union u w (up n) (up o)) (emb s)) := by
    rw [unionFirstInstance]
    exact h
  obtain ⟨h'⟩ := h'
  have r := Derivation.equalityElimination (union u w (up n) (up o)) (emb s) (emb t) e h'
  rw [unionFirstInstance] at r
  exact ⟨r⟩

/-- Rewrite along an equation inside the J atom. -/
theorem membershipRewrite {α : Type} {Γ : List (Formula α)} {s t : OTerm α}
    (e : D body Γ (eqn s t)) (h : D body Γ (membership true s)) : D body Γ (membership true t) := by
  obtain ⟨e⟩ := e
  have h' : D body Γ (instantiate (membership true w) (emb s)) := by
    rw [membershipInstance]
    exact h
  obtain ⟨h'⟩ := h'
  have r := Derivation.equalityElimination (membership true w) (emb s) (emb t) e h'
  rw [membershipInstance] at r
  exact ⟨r⟩

theorem eqnSymm {α : Type} {Γ : List (Formula α)} {s t : OTerm α}
    (e : D body Γ (eqn s t)) : D body Γ (eqn t s) := by
  obtain ⟨e⟩ := e
  exact ⟨ID1Completion.InternalTagArithmeticSupportProof.symm e⟩

end Logic

section Union
variable (d : Data) (c : Nat) (u : Program 2)

theorem outerRelabel {α β : Type} (m : OTerm α) (f : α → β) :
    (outer u m).relabel f = outer u (m.relabel f) := by
  rw [relabelEmb, outerSubst, termRelabel]

theorem innerInvRelabel {α β : Type} (m n : OTerm α) (f : α → β) :
    (innerInv u m n).relabel f = innerInv u (m.relabel f) (n.relabel f) := by
  rw [relabelEmb, innerInvSubst, termRelabel, termRelabel]

theorem outerInstance {α : Type} (t : OTerm α) :
    instantiate (outer u (w (α := α))) (emb t) = outer u t := by
  unfold instantiate
  rw [bindEmbedding, outerSubst, varBind]

theorem innerInvInstance {α : Type} (m t : OTerm α) :
    instantiate (innerInv u (up m) (w (α := α))) (emb t) = innerInv u m t := by
  unfold instantiate
  rw [bindEmbedding, innerInvSubst, liftBind, varBind]

theorem outerShape {α : Type} :
    replacedBody (sliceBody d c true) (outer u (w (α := α))) =
      carrier d true c (w (α := α)) ⊓ edgeOuter d c u (w (α := α)) := by
  rw [ID1Completion.InternalSliceInductionSyntaxProof.sliceReplacement]
  unfold PositiveArithmeticPredicateSubstitution.liftPredicateFormula
  rw [outerRelabel]
  rfl

theorem innerShape {α : Type} (m : OTerm α) :
    replacedBody (sliceBody d c true) (innerInv u (up m) (w (α := α))) =
      carrier d true c (w (α := α)) ⊓ edgeInner d c u (up m) (w (α := α)) := by
  rw [ID1Completion.InternalSliceInductionSyntaxProof.sliceReplacement]
  unfold PositiveArithmeticPredicateSubstitution.liftPredicateFormula
  rw [innerInvRelabel]
  unfold edgeInner innerInv up
  simp only [Term.relabel_relabel]
  rfl

/-- The split case analysis, in any context. -/
theorem splitCase {δ : Type} (Θ : List (Formula δ)) (M N M' N' O' : OTerm δ)
    (hOuter : D (sourceBody d c) Θ (edgeOuter d c u M))
    (hInner : D (sourceBody d c) Θ (edgeInner d c u M N))
    (hJ : D (sourceBody d c) Θ (membership true N))
    (hU : D (sourceBody d c) Θ (union u M' N' O'))
    (h1 : D (sourceBody d c) Θ ((edge d true c M M').not.imp (eqn M' M)))
    (h2 : D (sourceBody d c) Θ ((edge d true c N N').not.imp (eqn N' N)))
    (h3 : D (sourceBody d c) Θ ((edge d true c M M').not.imp (edge d true c N N'))) :
    D (sourceBody d c) Θ (membership true O') := by
  -- J N' in every case
  have jN' : D (sourceBody d c) Θ (membership true N') := by
    apply byCases (edge d true c N N')
    · have ih := allElim N' (cons (edge d true c N N') hInner)
      unfold edgeInner at ih
      rw [edgeInnerInstance] at ih
      exact andL (mp ih (hyp _))
    · have e := mp (cons _ h2) (hyp _)
      exact membershipRewrite (eqnSymm e) (cons _ hJ)
  apply byCases (edge d true c M M')
  · -- decreased first component: outer hypothesis at M'
    have ih := allElim M' (cons (edge d true c M M') hOuter)
    unfold edgeOuter at ih
    rw [edgeOuterInstance] at ih
    have out := mp ih (hyp _)
    have atN := allElim N' out
    unfold outer at atN
    rw [outerBodyInstance] at atN
    have inn := mp atN (cons _ jN')
    have atO := allElim O' inn
    unfold inner at atO
    rw [innerBodyInstance] at atO
    exact mp atO (cons _ hU)
  · -- unchanged first component, decreased second: inner hypothesis at N'
    have e1 := mp (cons _ h1) (hyp _)
    have e3 := mp (cons _ h3) (hyp _)
    have ih := allElim N' (cons (edge d true c M M').not hInner)
    unfold edgeInner at ih
    rw [edgeInnerInstance] at ih
    have inn := andR (mp ih e3)
    have atO := allElim O' inn
    unfold inner at atO
    rw [innerBodyInstance] at atO
    exact mp atO (unionRewrite u e1 (cons _ hU))

/-- After the split: two existential eliminations, then `splitCase`. -/
theorem afterSplit {γ : Type} (Θ : List (Formula γ)) (m n o' : OTerm γ)
    (hOuter : D (sourceBody d c) Θ (edgeOuter d c u m))
    (hInner : D (sourceBody d c) Θ (edgeInner d c u m n))
    (hJ : D (sourceBody d c) Θ (membership true n))
    (hS : D (sourceBody d c) Θ (splitFormula d c u m n o')) :
    D (sourceBody d c) Θ (membership true o') := by
  let φ2 : Formula ((γ ⊕ Fin 1) ⊕ Fin 1) := splitBody d c u
    ((m.relabel Sum.inl).relabel Sum.inl) ((n.relabel Sum.inl).relabel Sum.inl)
    ((o'.relabel Sum.inl).relabel Sum.inl) (.var (.inl (.inr 0))) (.var (.inr 0))
  let φ1 : Formula (γ ⊕ Fin 1) := existsOne φ2
  refine existsElim (φ := φ1) hS ?_
  have o1 := lift φ1 hOuter
  have i1 := lift φ1 hInner
  have j1 := lift φ1 hJ
  rw [edgeOuterRelabel] at o1
  rw [edgeInnerRelabel] at i1
  rw [membershipRelabel] at j1
  change D _ _ ((membership true o').relabel Sum.inl)
  rw [membershipRelabel]
  refine existsElim (φ := φ2) (hyp φ1) ?_
  have o2 := lift φ2 o1
  have i2 := lift φ2 i1
  have j2 := lift φ2 j1
  rw [edgeOuterRelabel] at o2
  rw [edgeInnerRelabel] at i2
  rw [membershipRelabel] at j2
  change D _ _ ((membership true (o'.relabel Sum.inl)).relabel Sum.inl)
  rw [membershipRelabel]
  have s := hyp (body := sourceBody d c) (Γ := (φ1 :: Θ.map weaken).map weaken) φ2
  exact splitCase d c u _ _ _ _ _ _ o2 i2 j2 (andL s) (andL (andR s)) (andL (andR (andR s)))
    (andR (andR (andR s)))

/-- J of a union, given the carriers, both induction hypotheses and J of the second component. -/
theorem unionMember (hCU : CarrierUnion d c u) (hMS : MultisetSplit d c u)
    {γ : Type} (Θ : List (Formula γ)) (m n o : OTerm γ)
    (hKm : D (sourceBody d c) Θ (carrier d true c m))
    (hKn : D (sourceBody d c) Θ (carrier d true c n))
    (hOuter : D (sourceBody d c) Θ (edgeOuter d c u m))
    (hInner : D (sourceBody d c) Θ (edgeInner d c u m n))
    (hJ : D (sourceBody d c) Θ (membership true n))
    (hU : D (sourceBody d c) Θ (union u m n o)) :
    D (sourceBody d c) Θ (membership true o) := by
  have hK := hCU γ Θ m n o hKm hKn hU
  refine ID1Completion.InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction
    d true c γ Θ o hK ?_
  apply allIntro
  apply intro
  let E := edge d true c (up o) (w (α := γ))
  have o1 := lift E hOuter
  have i1 := lift E hInner
  have j1 := lift E hJ
  have u1 := lift E hU
  rw [edgeOuterRelabel] at o1
  rw [edgeInnerRelabel] at i1
  rw [membershipRelabel] at j1
  rw [unionRelabel] at u1
  have s := hMS _ _ (up m) (up n) (up o) w u1 (hyp E)
  exact afterSplit d c u _ _ _ _ o1 i1 j1 s

/-- Inner induction: J n implies inner m n, given the carrier of m and the outer hypothesis at m. -/
theorem innerStep (hCU : CarrierUnion d c u) (hMS : MultisetSplit d c u)
    {β : Type} (Γ : List (Formula β)) (m : OTerm β)
    (hK : D (sourceBody d c) Γ (carrier d true c m))
    (hIH : D (sourceBody d c) Γ (edgeOuter d c u m)) (n : OTerm β)
    (hn : D (sourceBody d c) Γ (membership true n)) :
    D (sourceBody d c) Γ (inner u m n) := by
  let θ : Formula (β ⊕ Fin 1) := innerInv u (up m) w
  let H := replacedBody (sliceBody d c true) θ
  have premise : D (sourceBody d c) (H :: Γ.map weaken) θ := by
    have hH : D (sourceBody d c) (H :: Γ.map weaken) (carrier d true c w ⊓ edgeInner d c u (up m) w) := by
      rw [← innerShape d c u m]
      exact hyp H
    have hKv := andL hH
    have hIHv := andR hH
    have hK' := lift H hK
    have hIH' := lift H hIH
    rw [carrierRelabel] at hK'
    rw [edgeOuterRelabel] at hIH'
    -- (1) J of the current object
    have hJv : D (sourceBody d c) (H :: Γ.map weaken) (membership true w) := by
      refine ID1Completion.InternalAccessibilityRulesProof.actualOriginalAccessibilityIntroduction
        d true c _ _ w hKv ?_
      apply allIntro
      apply intro
      let E := edge d true c (up w) (w (α := β ⊕ Fin 1))
      have i1 := lift E hIHv
      rw [edgeInnerRelabel] at i1
      have ih := allElim w i1
      unfold edgeInner at ih
      rw [edgeInnerInstance] at ih
      have step : D (sourceBody d c) (E :: (H :: Γ.map weaken).map weaken)
          (edge d true c (up w) w) := hyp E
      exact andL (mp ih step)
    -- (2) inner m n at the current object
    refine andI hJv ?_
    apply allIntro
    apply intro
    let Uo := union u (up (up m)) (up w) (w (α := β ⊕ Fin 1))
    have k1 := lift Uo hK'
    have k2 := lift Uo hKv
    have o1 := lift Uo hIH'
    have i1 := lift Uo hIHv
    have j1 := lift Uo hJv
    rw [carrierRelabel] at k1 k2
    rw [edgeOuterRelabel] at o1
    rw [edgeInnerRelabel] at i1
    rw [membershipRelabel] at j1
    exact unionMember d c u hCU hMS _ (up (up m)) (up w) w k1 k2 o1 i1 j1 (hyp Uo)
  have ind := ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction d c β Γ true θ n premise
  change D _ _ ((membership true n).imp (instantiate (innerInv u (up m) w) (emb n))) at ind
  rw [innerInvInstance] at ind
  exact andR (mp ind hn)

theorem exact_ConditionalJUnion : ConditionalJUnion := by
  intro d c u hCU hMS α Γ m n o hm hn ho
  let θ : Formula (α ⊕ Fin 1) := outer u w
  let H := replacedBody (sliceBody d c true) θ
  have premise : D (sourceBody d c) (H :: Γ.map weaken) θ := by
    have hH : D (sourceBody d c) (H :: Γ.map weaken) (carrier d true c w ⊓ edgeOuter d c u w) := by
      rw [← outerShape d c u]
      exact hyp H
    apply allIntro
    apply intro
    let Jn := membership true (w (α := α ⊕ Fin 1))
    have k1 := lift Jn (andL hH)
    have o1 := lift Jn (andR hH)
    rw [carrierRelabel] at k1
    rw [edgeOuterRelabel] at o1
    exact innerStep d c u hCU hMS _ (up w) k1 o1 w (hyp Jn)
  have ind := ID1Completion.InternalSliceInductionProof.actualInternalSliceInduction d c α Γ true θ m premise
  change D _ _ ((membership true m).imp (instantiate (outer u w) (emb m))) at ind
  rw [outerInstance] at ind
  have om := mp ind hm
  have atN := allElim n om
  unfold outer at atN
  rw [outerBodyInstance] at atN
  have inn := mp atN hn
  have atO := allElim o inn
  unfold inner at atO
  rw [innerBodyInstance] at atO
  exact mp atO ho

#print axioms exact_ConditionalJUnion

end Union

end LogicLineages.PersistentMarking.ConditionalJUnionProof
