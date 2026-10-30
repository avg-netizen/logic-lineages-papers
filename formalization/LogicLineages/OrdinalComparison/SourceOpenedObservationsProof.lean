module
public import LogicLineages.OrdinalComparison.SourceOpenedObservationsTargets
public import LogicLineages.OrdinalComparison.SourceLocatedSubtermsProof
public import LogicLineages.OrdinalComparison.SourcePortContextsProof
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof
public import LogicLineages.OrdinalComparison.SourceStructural
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceOpenedObservationsProof
open SourceTypeSupport SourceTypeSupportProof SourceLocatedSubterms SourceLocatedSubtermsProof
open SourceTypedPorts SourceTypedPortsProof SourcePortContexts SourcePortContextsProof
open SourceOpenedObservations SourceOpenedObservationsTargets

theorem openedObservationMembership : OpenedObservationMembership := by
  intro Symbol arity Γ τ t B o
  constructor
  · intro hm
    obtain ⟨P, hp, hm⟩ := List.mem_flatMap.mp hm
    have hv : ValidPorts (typeSupport t) P := by
      have hh := (portContextEnumeration B (literalTypes t) P).mp hp
      rw [literalTypeEnumeration Symbol arity Γ τ t] at hh
      exact hh
    obtain ⟨u, hu, hm⟩ := List.mem_flatMap.mp hm
    by_cases h : u.ambient = u.binders ++ Γ
    · simp only [dif_pos h] at hm
      by_cases hb : P.length + lambdaDepth u.body ≤ B
      · simp only [if_pos hb] at hm
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact ⟨hv, u, hu, h, a, (typedAssignmentEnumeration _ _ a).mp ha, hb, rfl⟩
      · simp only [if_neg hb, List.not_mem_nil] at hm
    · simp only [dif_neg h, List.not_mem_nil] at hm
  · rintro ⟨hp, u, hu, h, a, ha, hb, he⟩
    apply List.mem_flatMap.mpr
    refine ⟨o.ports, ?_, ?_⟩
    · apply (portContextEnumeration B (literalTypes t) o.ports).mpr
      rw [literalTypeEnumeration Symbol arity Γ τ t]
      exact hp
    · apply List.mem_flatMap.mpr
      refine ⟨u, hu, ?_⟩
      simp only [dif_pos h, if_pos hb]
      exact List.mem_map.mpr ⟨a, (typedAssignmentEnumeration _ _ a).mpr ha, he.symm⟩

private theorem transport_support {Symbol : Type} {arity : Symbol → Nat} {Ξ Ζ : List Ty} {τ : Ty}
    (h : Ξ = Ζ) (t : Term Symbol arity Ξ τ) : typeSupport (transportContext h t) = typeSupport t := by
  cases h
  rfl

private theorem transport_depth {Symbol : Type} {arity : Symbol → Nat} {Ξ Ζ : List Ty} {τ : Ty}
    (h : Ξ = Ζ) (t : Term Symbol arity Ξ τ) : lambdaDepth (transportContext h t) = lambdaDepth t := by
  cases h
  rfl

private theorem open_support {Symbol : Type} {arity : Symbol → Nat} (Γ : List Ty) {B : Nat}
    (P : PortContext B) (u : LocatedTerm Symbol arity) (h : u.ambient = u.binders ++ Γ)
    (a : PortMap (portTypes P) u.binders) : typeSupport (openLocated Γ P u h a).body = typeSupport u.body :=
  ((supportDepthRenaming Symbol arity _ _ _ (transportContext h u.body) (renameWith Γ a)).1).trans
    (transport_support h u.body)

private theorem open_depth {Symbol : Type} {arity : Symbol → Nat} (Γ : List Ty) {B : Nat}
    (P : PortContext B) (u : LocatedTerm Symbol arity) (h : u.ambient = u.binders ++ Γ)
    (a : PortMap (portTypes P) u.binders) : lambdaDepth (openLocated Γ P u h a).body = lambdaDepth u.body :=
  ((supportDepthRenaming Symbol arity _ _ _ (transportContext h u.body) (renameWith Γ a)).2).trans
    (transport_depth h u.body)

theorem openedRootMembership : OpenedRootMembership := by
  intro Symbol arity Γ τ t B hb
  apply (openedObservationMembership Symbol arity Γ τ t B _).mpr
  refine ⟨by simp [ValidPorts], ⟨[], Γ, τ, t⟩, locatedRootMembership _ _ _ _ _ t, rfl,
    PortMap.nil, by simp [indices], ?_, ?_⟩
  · simpa only [List.length_nil, Nat.zero_add] using hb
  · change (⟨[], τ, t⟩ : Observation Symbol arity Γ B) =
      ⟨[], τ, t.rename (fun v => v)⟩
    exact congrArg (fun u : Term Symbol arity Γ τ => (⟨[], τ, u⟩ : Observation Symbol arity Γ B))
      (Term.rename_identity t).symm

theorem openedDepthBudget : OpenedDepthBudget := by
  intro Symbol arity Γ τ t B o ho
  obtain ⟨_, u, _, h, a, _, hb, he⟩ := (openedObservationMembership Symbol arity Γ τ t B o).mp ho
  have hd : lambdaDepth o.body = lambdaDepth u.body := by
    rw [he]
    exact open_depth Γ _ u h a
  simpa only [hd] using hb

theorem openedTypeSupport : OpenedTypeSupport := by
  intro Symbol arity Γ τ t B o ho
  obtain ⟨_, u, hu, h, a, _, _, he⟩ := (openedObservationMembership Symbol arity Γ τ t B o).mp ho
  have hs : typeSupport o.body = typeSupport u.body := by
    rw [he]
    exact open_support Γ _ u h a
  rw [hs]
  exact locatedTypeSupport Symbol arity Γ [] τ t u hu

private theorem plain_open_closure {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {τ : Ty} (t : Term Symbol arity Γ τ) (B : Nat) (P : PortContext B)
    (hp : ValidPorts (typeSupport t) P) (u : LocatedTerm Symbol arity)
    (hu : u ∈ collect [] t) (h : u.ambient = u.binders ++ Γ)
    (a : PortMap (portTypes P) u.binders) (ha : (indices a).Nodup)
    (hb : P.length + lambdaDepth u.body ≤ B) :
    ∀ v ∈ plainChildren (openLocated Γ P u h a), v ∈ observations B t := by
  rcases u with ⟨Λ, Ξ, υ, q⟩
  change Ξ = Λ ++ Γ at h
  subst Ξ
  cases q with
  | var | lam | zeroC | succC | caseC | recC => intro v hv; cases hv
  | app f q =>
    intro v hv
    change v ∈ [⟨P, _, f.rename (renameWith Γ a)⟩, ⟨P, _, q.rename (renameWith Γ a)⟩] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · apply (openedObservationMembership Symbol arity Γ τ t B _).mpr
      refine ⟨hp, ⟨Λ, Λ ++ Γ, _, f⟩, ?_, rfl, a, ha, ?_, rfl⟩
      · exact locatedChildClosure Symbol arity Γ [] τ t _ _ hu (by simp [children])
      · exact (Nat.add_le_add_left (Nat.le_max_left _ _) _).trans hb
    · apply (openedObservationMembership Symbol arity Γ τ t B _).mpr
      refine ⟨hp, ⟨Λ, Λ ++ Γ, _, q⟩, ?_, rfl, a, ha, ?_, rfl⟩
      · exact locatedChildClosure Symbol arity Γ [] τ t _ _ hu (by simp [children])
      · exact (Nat.add_le_add_left (Nat.le_max_right _ _) _).trans hb
  | ranked s args =>
    intro v hv
    change v ∈ List.ofFn (fun i : Fin (arity s) =>
      (⟨P, .ground, (args i).rename (renameWith Γ a)⟩ : Observation Symbol arity Γ B)) at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    apply (openedObservationMembership Symbol arity Γ τ t B _).mpr
    refine ⟨hp, ⟨Λ, Λ ++ Γ, _, args i⟩, ?_, rfl, a, ha, ?_, rfl⟩
    · exact locatedChildClosure Symbol arity Γ [] τ t _ _ hu (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · exact (Nat.add_le_add_left (Finset.le_sup (f := fun j => lambdaDepth (args j)) (Finset.mem_univ i)) _).trans hb

theorem openedPlainChildClosure : OpenedPlainChildClosure := by
  intro Symbol arity Γ τ t B o v ho hv
  obtain ⟨hp, u, hu, h, a, ha, hb, he⟩ := (openedObservationMembership Symbol arity Γ τ t B o).mp ho
  exact plain_open_closure t B o.ports hp u hu h a ha hb v (by rw [← he]; exact hv)

private theorem observation_body_inj {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {B : Nat} {P : PortContext B} {τ : Ty} {s t : Term Symbol arity (portTypes P ++ Γ) τ}
    (h : (⟨P, τ, s⟩ : Observation Symbol arity Γ B) = ⟨P, τ, t⟩) : s = t := by
  cases h
  rfl

private theorem lambda_open_closure {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    {τ : Ty} (t : Term Symbol arity Γ τ) (B : Nat) (P : PortContext B)
    (hp : ValidPorts (typeSupport t) P) (u : LocatedTerm Symbol arity)
    (hu : u ∈ collect [] t) (h : u.ambient = u.binders ++ Γ)
    (a : PortMap (portTypes P) u.binders) (ha : (indices a).Nodup)
    (hb : P.length + lambdaDepth u.body ≤ B) (σ υ : Ty)
    (body : Term Symbol arity (σ :: (portTypes P ++ Γ)) υ)
    (he : (⟨P, .arrow σ υ, .lam body⟩ : Observation Symbol arity Γ B) = openLocated Γ P u h a) :
    ∀ i : Fin B, i ∉ P.map Prod.fst →
      (⟨(i, σ) :: P, υ, body⟩ : Observation Symbol arity Γ B) ∈ observations B t := by
  rcases u with ⟨Λ, Ξ, ρ, q⟩
  change Ξ = Λ ++ Γ at h
  subst Ξ
  cases q with
  | var | app | zeroC | succC | caseC | recC | ranked => cases he
  | lam qbody =>
    rename_i σ' υ'
    have ht : Ty.arrow σ υ = Ty.arrow σ' υ' := congrArg Observation.resultType he
    obtain ⟨hσ, hυ⟩ := Ty.arrow.inj ht
    subst σ'
    subst υ'
    have heq : body = qbody.rename (Renaming.lift (renameWith Γ a)) :=
      Term.lam.inj (observation_body_inj he)
    subst body
    intro i hi
    have hσ : σ ∈ typeSupport t := by
      apply locatedTypeSupport Symbol arity Γ [] τ t _ hu
      exact (literalBinderSupport Symbol arity _ σ υ qbody).2.1
        (List.mem_toFinset.mpr (Ty.mem_subtypes_self σ))
    have hp' := (freshPortExtension B (typeSupport t) P i σ hp hi hσ).1
    apply (openedObservationMembership Symbol arity Γ τ t B _).mpr
    refine ⟨hp', ⟨σ :: Λ, σ :: (Λ ++ Γ), υ, qbody⟩, ?_, rfl, liftMap σ a,
      (assignmentLift Γ (portTypes P) Λ σ a).1 ha, ?_, ?_⟩
    · exact locatedChildClosure Symbol arity Γ [] τ t _ _ hu (by simp [children])
    · change P.length + 1 + lambdaDepth qbody ≤ B
      change P.length + (lambdaDepth qbody + 1) ≤ B at hb
      omega
    · change (⟨(i, σ) :: P, υ, qbody.rename (Renaming.lift (renameWith Γ a))⟩ : Observation Symbol arity Γ B) =
        ⟨(i, σ) :: P, υ, qbody.rename (renameWith Γ (liftMap σ a))⟩
      rw [(assignmentLift Γ (portTypes P) Λ σ a).2]

theorem openedLambdaClosure : OpenedLambdaClosure := by
  intro Symbol arity Γ τ t B P σ υ body hm
  have hd := openedDepthBudget Symbol arity Γ τ t B _ hm
  have hlen : P.length < B := by
    change P.length + (lambdaDepth body + 1) ≤ B at hd
    omega
  obtain ⟨hp, u, hu, h, a, ha, hb, he⟩ := (openedObservationMembership Symbol arity Γ τ t B _).mp hm
  exact ⟨freshPortAvailability B P hp.1 hlen,
    lambda_open_closure t B P hp u hu h a ha hb σ υ body he⟩

end LogicLineages.OrdinalComparison.Source.SourceOpenedObservationsProof
