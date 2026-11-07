module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalComputabilityApplication InternalComputabilityApplicationSyntaxProof
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalRecursionClosureSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (emb z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem typedness (data : JointGammaComputability.Data) (tau : Ty) (context t : OTerm α)
    (h : Nonempty (Derivation body Gamma (computable data tau context t))) :
    Nonempty (Derivation body Gamma (typed data tau context t)) := by
  obtain ⟨h⟩ := h
  cases tau with
  | ground =>
    rw [computable,← embedPair,JointGammaComputability.formula,conjunctionSubst] at h
    have ht := Derivation.conjunctionLeft h
    rw [typedInstance] at ht
    exact ⟨ht⟩
  | arrow sigma tau =>
    rw [computableArrow] at h
    exact ⟨Derivation.conjunctionLeft h⟩

theorem arrowElimination (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α)
    (hf : Nonempty (Derivation body Gamma (computable data (.arrow sigma tau) context f)))
    (hg : Nonempty (Derivation body Gamma (guarded data f a)))
    (ha : Nonempty (Derivation body Gamma (computable data sigma context a))) :
    Nonempty (Derivation body Gamma (resultExists data sigma tau context f a)) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  obtain ⟨ha⟩ := ha
  rw [computableArrow] at hf
  have h := Derivation.universalElimination (emb a) (Derivation.conjunctionRight hf)
  rw [arrowBodyInstantiate] at h
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hg) ha⟩

theorem arrowFromPremises (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α)
    (h : Nonempty (Derivation body Gamma (premises data sigma tau context f a))) :
    Nonempty (Derivation body Gamma (resultExists data sigma tau context f a)) := by
  obtain ⟨h⟩ := h
  exact arrowElimination data sigma tau context f a
    ⟨Derivation.conjunctionLeft h⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩

/-- Equality elimination applies to the whole original formula. No positivity
assumption is imposed on its higher-type occurrences of the ID1 predicate. -/
theorem computableTransport (data : JointGammaComputability.Data) (tau : Ty)
    (context out other : OTerm α)
    (he : Nonempty (Derivation body Gamma (eqn out other)))
    (hc : Nonempty (Derivation body Gamma (computable data tau context out))) :
    Nonempty (Derivation body Gamma (computable data tau context other)) := by
  obtain ⟨he⟩ := he
  obtain ⟨hc⟩ := hc
  have hi : Derivation body Gamma
      (instantiate (computable data tau (context.relabel Sum.inl) (.var (.inr 0))) (emb out)) := by
    rw [computableInstantiate]
    exact hc
  have h := Derivation.equalityElimination
    (computable data tau (context.relabel Sum.inl) (.var (.inr 0))) (emb out) (emb other) he hi
  rw [computableInstantiate] at h
  exact ⟨h⟩

/-- The existential rule retains both original conjuncts at the same fresh
raw result code. No standard-natural witness is selected. -/
theorem resultCases (data : JointGammaComputability.Data) (sigma tau : Ty)
    (context f a : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (resultExists data sigma tau context f a)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (v : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (accepted data sigma tau (context.relabel j) (f.relabel j) (a.relabel j) v)) →
      Nonempty (Derivation body Delta (computable data tau (context.relabel j) v)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := resultBody data sigma tau context f a
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem activeApplication (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (sigma tau : Ty)
    (context f a out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (activationAt old window arrow context sigma tau f a)))
    (hp : Nonempty (Derivation body Gamma
      (premises (InternalApplication.computability old window arrow result) sigma tau context f a)))
    (ho : Nonempty (Derivation body Gamma
      (accepted (InternalApplication.computability old window arrow result) sigma tau context f a out))) :
    Nonempty (Derivation body Gamma
      (computable (InternalApplication.computability old window arrow result) tau context out)) := by
  let data := InternalApplication.computability old window arrow result
  apply resultCases data sigma tau context f a _ (arrowFromPremises data sigma tau context f a hp)
  intro β j Delta value hj hv hcv
  rw [computableRename]
  have hc' := renameInto hc j Delta hj
  rw [activationRename] at hc'
  have ho' := renameInto ho j Delta hj
  rw [acceptedRename] at ho'
  have he := InternalApplicationProof.activeFunctionality
    (ApplicationDomain.activation window old.typed old.guard arrow) result old.application
    (arguments (context.relabel j) sigma tau (f.relabel j) (a.relabel j))
    value (out.relabel j) hc' hv ho'
  rw [equalEqn] at he
  exact computableTransport data tau (context.relabel j) value (out.relabel j) he hcv

theorem activeResult (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (sigma tau : Ty)
    (context f a out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (activationAt old window arrow context sigma tau f a)))
    (hp : Nonempty (Derivation body Gamma
      (premises (InternalApplication.computability old window arrow result) sigma tau context f a)))
    (hr : Nonempty (Derivation body Gamma (programGraph result out (arguments context sigma tau f a)))) :
    Nonempty (Derivation body Gamma
      (computable (InternalApplication.computability old window arrow result) tau context out)) :=
  activeApplication old window arrow result sigma tau context f a out hc hp
    (InternalApplicationGraphProof.activeAccept
      (ApplicationDomain.activation window old.typed old.guard arrow) result old.application
      (arguments context sigma tau f a) out hc hr)

theorem activation (data : JointGammaComputability.Data) (window : Program 1) (arrow : Program 2)
    (sigma tau : Ty) (context f a : OTerm α)
    (hm : Nonempty (Derivation body Gamma (metadata window arrow context sigma tau)))
    (hp : Nonempty (Derivation body Gamma (premises data sigma tau context f a))) :
    Nonempty (Derivation body Gamma (activationAt data window arrow context sigma tau f a)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hp⟩ := hp
  exact ApplicationGuardedActivationProof.activationAt window data.typed data.guard arrow
    context (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (numeral (typeNumber (.arrow sigma tau))) f a
    ⟨Derivation.conjunctionLeft hm⟩ ⟨Derivation.conjunctionRight hm⟩
    (typedness data (.arrow sigma tau) context f ⟨Derivation.conjunctionLeft hp⟩)
    (typedness data sigma context a ⟨Derivation.conjunctionRight (Derivation.conjunctionRight hp)⟩)
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight hp)⟩

theorem applicationComputability (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (sigma tau : Ty)
    (context f a out : OTerm α)
    (hm : Nonempty (Derivation body Gamma (metadata window arrow context sigma tau)))
    (hp : Nonempty (Derivation body Gamma
      (premises (InternalApplication.computability old window arrow result) sigma tau context f a)))
    (ho : Nonempty (Derivation body Gamma
      (accepted (InternalApplication.computability old window arrow result) sigma tau context f a out))) :
    Nonempty (Derivation body Gamma
      (computable (InternalApplication.computability old window arrow result) tau context out)) :=
  activeApplication old window arrow result sigma tau context f a out
    (activation (InternalApplication.computability old window arrow result) window arrow
      sigma tau context f a hm hp) hp ho

theorem resultComputability (old : JointGammaComputability.Data)
    (window : Program 1) (arrow : Program 2) (result : Program 5) (sigma tau : Ty)
    (context f a out : OTerm α)
    (hm : Nonempty (Derivation body Gamma (metadata window arrow context sigma tau)))
    (hp : Nonempty (Derivation body Gamma
      (premises (InternalApplication.computability old window arrow result) sigma tau context f a)))
    (hr : Nonempty (Derivation body Gamma (programGraph result out (arguments context sigma tau f a)))) :
    Nonempty (Derivation body Gamma
      (computable (InternalApplication.computability old window arrow result) tau context out)) :=
  activeResult old window arrow result sigma tau context f a out
    (activation (InternalApplication.computability old window arrow result) window arrow
      sigma tau context f a hm hp) hp hr

theorem actualOriginalComputabilityTypedness :
    InternalComputabilityApplicationTargets.ActualOriginalComputabilityTypedness := by
  intro body data α tau context t
  obtain ⟨d⟩ := typedness (body := body) (Gamma := [computable data tau context t]) data tau context t
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalArrowElimination :
    InternalComputabilityApplicationTargets.ActualOriginalArrowElimination := by
  intro body data α sigma tau context f a
  obtain ⟨d⟩ := arrowFromPremises (body := body) (Gamma := [premises data sigma tau context f a])
    data sigma tau context f a ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

theorem actualOriginalActiveApplicationComputability :
    InternalComputabilityApplicationTargets.ActualOriginalActiveApplicationComputability := by
  intro body old window arrow result α sigma tau context f a out
  let data := InternalApplication.computability old window arrow result
  let A := activationAt old window arrow context sigma tau f a
  let P := premises data sigma tau context f a
  let R := accepted data sigma tau context f a out
  obtain ⟨d⟩ := activeApplication (body := body) (Gamma := [R,P,A])
    old window arrow result sigma tau context f a out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction d))⟩

theorem actualOriginalActiveResultComputability :
    InternalComputabilityApplicationTargets.ActualOriginalActiveResultComputability := by
  intro body old window arrow result α sigma tau context f a out
  let data := InternalApplication.computability old window arrow result
  let A := activationAt old window arrow context sigma tau f a
  let P := premises data sigma tau context f a
  let R := programGraph result out (arguments context sigma tau f a)
  obtain ⟨d⟩ := activeResult (body := body) (Gamma := [R,P,A])
    old window arrow result sigma tau context f a out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction d))⟩

theorem actualOriginalActivationBridge :
    InternalComputabilityApplicationTargets.ActualOriginalActivationBridge := by
  intro body data window arrow α sigma tau context f a
  let M := metadata window arrow context sigma tau
  let P := premises data sigma tau context f a
  obtain ⟨d⟩ := activation (body := body) (Gamma := [P,M]) data window arrow sigma tau context f a
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem actualOriginalApplicationComputability :
    InternalComputabilityApplicationTargets.ActualOriginalApplicationComputability := by
  intro body old window arrow result α sigma tau context f a out
  let data := InternalApplication.computability old window arrow result
  let M := metadata window arrow context sigma tau
  let P := premises data sigma tau context f a
  let R := accepted data sigma tau context f a out
  obtain ⟨d⟩ := applicationComputability (body := body) (Gamma := [R,P,M])
    old window arrow result sigma tau context f a out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction d))⟩

theorem actualOriginalResultComputability :
    InternalComputabilityApplicationTargets.ActualOriginalResultComputability := by
  intro body old window arrow result α sigma tau context f a out
  let data := InternalApplication.computability old window arrow result
  let M := metadata window arrow context sigma tau
  let P := premises data sigma tau context f a
  let R := programGraph result out (arguments context sigma tau f a)
  obtain ⟨d⟩ := resultComputability (body := body) (Gamma := [R,P,M])
    old window arrow result sigma tau context f a out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction d))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationProof
