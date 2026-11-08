module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof InternalComputabilityApplication InternalAccessibilityRules
open InternalComputabilityDownward InternalComputabilityDownwardSyntaxProof
open InternalComputabilityApplicationSyntaxProof InternalComputabilityApplicationProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof
open GuardedSourceSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem conjunction {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    {p q : Formula α} (hp : Nonempty (Derivation body Gamma p))
    (hq : Nonempty (Derivation body Gamma q)) : Nonempty (Derivation body Gamma (p ⊓ q)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction hp hq⟩

theorem actualOriginalArrowIntroduction :
    InternalComputabilityDownwardTargets.ActualOriginalArrowIntroduction := by
  intro body comp α Gamma sigma tau context f ⟨ht⟩ ⟨hstep⟩
  rw [computableArrow]
  exact ⟨Derivation.conjunctionIntroduction ht
    (Derivation.universalIntroduction
      (Derivation.implicationIntroduction (Derivation.implicationIntroduction hstep)))⟩

theorem resultIntroduction {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (sigma tau : Ty) (context f a out : OTerm α)
    (ha : Nonempty (Derivation body Gamma (accepted comp sigma tau context f a out)))
    (hc : Nonempty (Derivation body Gamma (computable comp tau context out))) :
    Nonempty (Derivation body Gamma (resultExists comp sigma tau context f a)) := by
  obtain ⟨h⟩ := conjunction ha hc
  exact ⟨Derivation.existentialIntroduction (emb out)
    (by rw [resultBodyInstantiate]; exact h)⟩

theorem applicationCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (f a : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (applicationExists comp context sigma tau f a)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (accepted comp sigma tau (numeral context) (f.relabel j) (a.relabel j) v)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := accepted comp sigma tau (numeral context)
    (f.relabel Sum.inl) (a.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (P :: Gamma.map weaken) (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem edgeCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (src : SourcePresentation.Data) (context : Nat) (f g : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (edge src false context f g)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (certificate src false context (f.relabel j) (g.relabel j) v)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  rw [InternalAccessibilityRulesSyntaxProof.edgeExists] at h
  let P := certificate src false context (f.relabel Sum.inl) (g.relabel Sum.inl)
    (.var (.inr (0 : Fin 1)))
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl (P :: Gamma.map weaken) (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

/-- The input and transformed certificates are both object-language witnesses.
Primitive-recursive totality is used only to supply the transformed graph output. -/
theorem actualOriginalCertifiedLiftReduction :
    InternalComputabilityDownwardTargets.ActualOriginalCertifiedLiftReduction := by
  intro src comp lift context hl α sigma tau f g a out other
  let P := (domain comp context sigma tau f a ⊓ edge src false context f g) ⊓
    (accepted comp sigma tau (numeral context) f a out ⊓
      accepted comp sigma tau (numeral context) g a other)
  have hp : Derivation (SourcePresentation.sourceBody src context) [P] P :=
    Derivation.hypothesis List.mem_cons_self
  have hd := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionLeft hp))
  have hr := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionLeft hp))
  have ho := Nonempty.intro (Derivation.conjunctionLeft (Derivation.conjunctionRight hp))
  have hq := Nonempty.intro (Derivation.conjunctionRight (Derivation.conjunctionRight hp))
  suffices h : Nonempty (Derivation (SourcePresentation.sourceBody src context) [P]
      (edge src false context out other)) by
    obtain ⟨h⟩ := h
    exact ⟨Derivation.implicationIntroduction h⟩
  apply edgeCases src context f g _ hr
  intro β j Delta witness hj hw
  rw [edgeRename]
  have hd' := renameInto hd j Delta hj
  have ho' := renameInto ho j Delta hj
  have hq' := renameInto hq j Delta hj
  simp only [domainRename,acceptedRename,numeralRename] at hd' ho' hq'
  apply programCases lift (liftArguments context sigma tau (a.relabel j) witness) _
  intro γ k Omega lifted hk hlift
  rw [edgeRename]
  rw [liftArgumentsRename] at hlift
  have hd'' := renameInto hd' k Omega hk
  have ho'' := renameInto ho' k Omega hk
  have hq'' := renameInto hq' k Omega hk
  have hw' := renameInto hw k Omega hk
  simp only [domainRename,acceptedRename,numeralRename,certificateRename] at hd'' ho'' hq'' hw'
  exact InternalAccessibilityRulesProof.edgeIntroduction
    (closedApply (hl γ sigma tau _ _ _ _ _ _ lifted)
      (conjunction (conjunction hd'' hw') (conjunction (conjunction ho'' hq'') hlift)))

/-- The codomain induction hypothesis is used only after the two original
application witnesses have been related by the arithmetic compatibility rule. -/
theorem transferApplication (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty) (rules : ArithmeticRules src comp context)
    (hl : ApplicationCompatibility src comp context)
    (ih : ∀ (α : Type) (Gamma : List (Formula α)) (f g : OTerm α),
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
        (computable comp tau (numeral context) f)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (edge src false context f g)) →
      Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
        (computable comp tau (numeral context) g)))
    {α : Type} {Gamma : List (Formula α)} (f g a : OTerm α)
    (hf : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computable comp (.arrow sigma tau) (numeral context) f)))
    (hr : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (edge src false context f g)))
    (hg : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma (guarded comp g a)))
    (ha : Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (computable comp sigma (numeral context) a))) :
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
      (resultExists comp sigma tau (numeral context) g a)) := by
  have htf := typedness comp (.arrow sigma tau) (numeral context) f hf
  have hta := typedness comp sigma (numeral context) a ha
  have htg := closedApply (rules.typedDown α (.arrow sigma tau) f g) (conjunction htf hr)
  have hguard := closedApply (rules.guardBack α (.arrow sigma tau) f g a)
    (conjunction (conjunction htf hr) hg)
  have hdomain := conjunction (conjunction htf hta) hguard
  have htotal := closedApply (rules.applicationTotal α sigma tau g a)
    (conjunction (conjunction htg hta) hg)
  have hresult := arrowElimination comp sigma tau (numeral context) f a hf hguard ha
  apply resultCases comp sigma tau (numeral context) f a _ hresult
  intro β j Delta out hj hout hcout
  simp only [resultExistsRename,numeralRename]
  simp only [numeralRename] at hout hcout
  have htotal' := renameInto htotal j Delta hj
  rw [applicationExistsRename] at htotal'
  have hd' := renameInto hdomain j Delta hj
  change Nonempty (Derivation _ _ ((domain comp context sigma tau f a).relabel j)) at hd'
  rw [domainRename] at hd'
  have hr' := renameInto hr j Delta hj
  rw [edgeRename] at hr'
  apply applicationCases comp context sigma tau (g.relabel j) (a.relabel j) _ htotal'
  intro γ k Omega other hk hother
  simp only [resultExistsRename,numeralRename]
  have hd'' := renameInto hd' k Omega hk
  have hr'' := renameInto hr' k Omega hk
  have hout' := renameInto hout k Omega hk
  have hcout' := renameInto hcout k Omega hk
  simp only [domainRename,edgeRename,acceptedRename,computableRename,numeralRename]
    at hd'' hr'' hout' hcout'
  have hedge := closedApply (hl γ sigma tau _ _ _ _ other)
    (conjunction (conjunction hd'' hr'') (conjunction hout' hother))
  exact resultIntroduction comp sigma tau (numeral context) _ _ other hother
    (ih γ Omega _ other hcout' hedge)

theorem actualOriginalComputabilityDownward :
    InternalComputabilityDownwardTargets.ActualOriginalComputabilityDownward := by
  intro src comp context rules hl tau
  induction tau with
  | ground =>
    intro α Gamma f g ⟨hf⟩ hr
    rw [computableGround] at hf
    have htyped := closedApply (rules.typedDown α .ground f g)
      (conjunction ⟨Derivation.conjunctionLeft hf⟩ hr)
    have hi := InternalAccessibilityRulesProof.actualOriginalSuccessorClosure
      src false context α Gamma f g ⟨Derivation.conjunctionRight hf⟩ hr
    rw [computableGround]
    exact conjunction htyped hi
  | arrow sigma tau _ ih =>
    intro α Gamma f g hf hr
    have htyped := closedApply (rules.typedDown α (.arrow sigma tau) f g)
      (conjunction (typedness comp (.arrow sigma tau) (numeral context) f hf) hr)
    apply actualOriginalArrowIntroduction (SourcePresentation.sourceBody src context)
      comp α Gamma sigma tau (numeral context) g htyped
    simp only [numeralRename]
    let Delta := computable comp sigma (numeral context) (.var (.inr (0 : Fin 1))) ::
      guarded comp (g.relabel Sum.inl) (.var (.inr (0 : Fin 1))) :: Gamma.map weaken
    have hj (p : Formula α) (hp : p ∈ Gamma) : p.relabel Sum.inl ∈ Delta :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    have hf' := renameInto hf Sum.inl Delta hj
    have hr' := renameInto hr Sum.inl Delta hj
    simp only [computableRename,numeralRename,edgeRename] at hf' hr'
    exact transferApplication src comp context sigma tau rules hl ih
      (α := α ⊕ Fin 1) (Gamma := Delta) (f.relabel Sum.inl) (g.relabel Sum.inl)
      (.var (.inr 0)) hf' hr'
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof
