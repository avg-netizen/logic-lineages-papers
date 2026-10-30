module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextTransport
public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingProof
public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowContextTransportProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowContextTransport

private theorem mapSome {α β : Type} (f : α → β) (o : Option α) (b : β) :
    o.map f=some b ↔ ∃ a, o=some a ∧ f a=b := by cases o <;> simp
private theorem twoSome {α β γ : Type} (f : α → β → γ) (o : Option α) (p : Option β) (c : γ) :
    (do let a ← o; let b ← p; pure (f a b))=some c ↔ ∃ a b, o=some a ∧ p=some b ∧ f a b=c := by
  cases o <;> cases p <;> simp
private theorem hasMap {α β : Type} (f : α → β) (o : Option α) :
    (∃ b, o.map f=some b) ↔ ∃ a, o=some a := by cases o <;> simp
private theorem hasTwo {α β γ : Type} (f : α → β → γ) (o : Option α) (p : Option β) :
    (∃ c, (do let a ← o; let b ← p; pure (f a b))=some c) ↔ (∃ a,o=some a) ∧ (∃ b,p=some b) := by
  cases o <;> cases p <;> simp
private theorem unionBound (s t : Finset Nat) (m : Nat) :
    (∀ i∈s∪t,i<m) ↔ (∀ i∈s,i<m) ∧ (∀ i∈t,i<m) := by simp [or_imp,forall_and]
private theorem unbindBound (s : Finset Nat) (m : Nat) :
    (∀ i∈unbind s,i<m) ↔ ∀ i∈s,i<m+1 := by
  constructor
  · intro h i hi
    cases i with
    | zero => omega
    | succ i => have hb := h i ((GorbowFreeSupportProof.unbindMembership s i).mpr hi); omega
  · intro h i hi
    have hb := h (i+1) ((GorbowFreeSupportProof.unbindMembership s i).mp hi)
    omega

private theorem termDomain (n : Nat) (t : Term n) (m : Nat) :
    (∃ u, term m t=some u) ↔ ∀ i∈termSupport t,i<m := by
  induction t with
  | var i => by_cases h : i.val<m <;> simp [term,termSupport,h]
  | zero => simp [term,termSupport]
  | succ t ih | universalFunction t ih => simpa only [term,hasMap,termSupport] using ih
  | add t u ht hu | mul t u ht hu => simp only [term,hasTwo,termSupport,unionBound,ht,hu]

private theorem formulaDomain (n : Nat) (φ : Formula n) : ∀ m,
    (∃ ψ, formula m φ=some ψ) ↔ ∀ i∈formulaSupport φ,i<m := by
  induction φ with
  | equal t u | knowledge t u => intro m; simp only [formula,hasTwo,formulaSupport,unionBound,termDomain]
  | universalRelation t | agent t | knowledgeAll t | truth t => intro m; simp only [formula,hasMap,formulaSupport,termDomain]
  | neg φ ih => intro m; simpa only [formula,hasMap,formulaSupport] using ih m
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
    intro m; simp only [formula,hasTwo,formulaSupport,unionBound,hφ m,hψ m]
  | all φ ih | ex φ ih => intro m; simpa only [formula,hasMap,formulaSupport,unbindBound] using ih (m+1)

theorem exactDomain : Comparators.GorbowContextTransport.ExactDomain :=
  ⟨fun n m t => termDomain n t m,fun n m φ => formulaDomain n φ m⟩

private theorem termTransfer (n : Nat) (t : Term n) : ∀ m (u : Term m), term m t=some u →
    GorbowTermPrefixCode.encode t=GorbowTermPrefixCode.encode u ∧ termSupport t=termSupport u ∧
    ∀ I ρ τ, (∀ (i : Fin n) (j : Fin m), i.val=j.val → i.val∈termSupport t → ρ i=τ j) → t.realize I ρ=u.realize I τ := by
  induction t with
  | var i =>
    intro m u h
    by_cases hv : i.val<m
    · have he : Term.var (⟨i.val,hv⟩ : Fin m)=u := by simpa [term,hv] using h
      subst u
      refine ⟨rfl,rfl,?_⟩
      intro I ρ τ ha
      exact ha i ⟨i.val,hv⟩ rfl (by simp [termSupport])
    · simp [term,hv] at h
  | zero =>
    intro m u h
    have he : Term.zero=u := by simpa [term] using h
    subst u
    exact ⟨rfl,rfl,fun _ _ _ _ => rfl⟩
  | succ t ih =>
    intro m u h
    obtain ⟨a,ha,he⟩ := (mapSome Term.succ (term m t) u).mp h
    subst u
    obtain ⟨hc,hs,hv⟩ := ih m a ha
    refine ⟨by simp [GorbowTermPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Term.realize,hv I ρ τ hh]
  | universalFunction t ih =>
    intro m u h
    obtain ⟨a,ha,he⟩ := (mapSome Term.universalFunction (term m t) u).mp h
    subst u
    obtain ⟨hc,hs,hv⟩ := ih m a ha
    refine ⟨by simp [GorbowTermPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Term.realize,hv I ρ τ hh]
  | add t u ht hu =>
    intro m w h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Term.add (term m t) (term m u) w).mp h
    subst w
    obtain ⟨hca,hsa,hva⟩ := ht m a ha
    obtain ⟨hcb,hsb,hvb⟩ := hu m b hb
    refine ⟨by simp [GorbowTermPrefixCode.encode,hca,hcb],by simp [termSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Term.realize,ea,eb]
  | mul t u ht hu =>
    intro m w h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Term.mul (term m t) (term m u) w).mp h
    subst w
    obtain ⟨hca,hsa,hva⟩ := ht m a ha
    obtain ⟨hcb,hsb,hvb⟩ := hu m b hb
    refine ⟨by simp [GorbowTermPrefixCode.encode,hca,hcb],by simp [termSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Term.realize,ea,eb]

private theorem formulaTransfer (n : Nat) (φ : Formula n) : ∀ m (ψ : Formula m), formula m φ=some ψ →
    GorbowFormulaPrefixCode.encode φ=GorbowFormulaPrefixCode.encode ψ ∧ formulaSupport φ=formulaSupport ψ ∧
    ∀ I ρ τ, (∀ (i : Fin n) (j : Fin m), i.val=j.val → i.val∈formulaSupport φ → ρ i=τ j) → (φ.realize I ρ ↔ ψ.realize I τ) := by
  induction φ with
  | equal t u =>
    intro m ψ h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.equal (term m t) (term m u) ψ).mp h
    subst ψ
    obtain ⟨hca,hsa,hva⟩ := termTransfer _ t m a ha
    obtain ⟨hcb,hsb,hvb⟩ := termTransfer _ u m b hb
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hca,hcb],by simp [formulaSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Formula.realize,ea,eb]
  | knowledge t u =>
    intro m ψ h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.knowledge (term m t) (term m u) ψ).mp h
    subst ψ
    obtain ⟨hca,hsa,hva⟩ := termTransfer _ t m a ha
    obtain ⟨hcb,hsb,hvb⟩ := termTransfer _ u m b hb
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hca,hcb],by simp [formulaSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Formula.realize,ea,eb]
  | universalRelation t =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.universalRelation (term m t) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := termTransfer _ t m a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Formula.realize,hv I ρ τ hh]
  | agent t =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.agent (term m t) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := termTransfer _ t m a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Formula.realize,hv I ρ τ hh]
  | knowledgeAll t =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.knowledgeAll (term m t) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := termTransfer _ t m a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Formula.realize,hv I ρ τ hh]
  | truth t =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.truth (term m t) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := termTransfer _ t m a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    simp only [Formula.realize,hv I ρ τ hh]
  | neg φ ih =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.neg (formula m φ) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := ih m a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],hs,?_⟩
    intro I ρ τ hh
    exact not_congr (hv I ρ τ hh)
  | imp φ ψ hφ hψ =>
    intro m χ h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.imp (formula m φ) (formula m ψ) χ).mp h
    subst χ
    obtain ⟨hca,hsa,hva⟩ := hφ m a ha
    obtain ⟨hcb,hsb,hvb⟩ := hψ m b hb
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hca,hcb],by simp [formulaSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Formula.realize,ea,eb]
  | conj φ ψ hφ hψ =>
    intro m χ h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.conj (formula m φ) (formula m ψ) χ).mp h
    subst χ
    obtain ⟨hca,hsa,hva⟩ := hφ m a ha
    obtain ⟨hcb,hsb,hvb⟩ := hψ m b hb
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hca,hcb],by simp [formulaSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Formula.realize,ea,eb]
  | disj φ ψ hφ hψ =>
    intro m χ h
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.disj (formula m φ) (formula m ψ) χ).mp h
    subst χ
    obtain ⟨hca,hsa,hva⟩ := hφ m a ha
    obtain ⟨hcb,hsb,hvb⟩ := hψ m b hb
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hca,hcb],by simp [formulaSupport,hsa,hsb],?_⟩
    intro I ρ τ hh
    have ea := hva I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_left _ hi))
    have eb := hvb I ρ τ (fun i j he hi => hh i j he (Finset.mem_union_right _ hi))
    simp only [Formula.realize,ea,eb]
  | all φ ih =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.all (formula (m+1) φ) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := ih (m+1) a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],by simp [formulaSupport,hs],?_⟩
    intro I ρ τ hh
    apply forall_congr'
    intro x
    apply hv I (Fin.cases x ρ) (Fin.cases x τ)
    intro i j he hi
    cases i using Fin.cases with
    | zero =>
      have hj : j=0 := Fin.ext (by simpa using he.symm)
      subst j
      rfl
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at he
      | succ j =>
        exact hh i j (by simpa using he) ((GorbowFreeSupportProof.unbindMembership _ i.val).mpr hi)
  | ex φ ih =>
    intro m ψ h
    obtain ⟨a,ha,he⟩ := (mapSome Formula.ex (formula (m+1) φ) ψ).mp h
    subst ψ
    obtain ⟨hc,hs,hv⟩ := ih (m+1) a ha
    refine ⟨by simp [GorbowFormulaPrefixCode.encode,hc],by simp [formulaSupport,hs],?_⟩
    intro I ρ τ hh
    apply exists_congr
    intro x
    apply hv I (Fin.cases x ρ) (Fin.cases x τ)
    intro i j he hi
    cases i using Fin.cases with
    | zero =>
      have hj : j=0 := Fin.ext (by simpa using he.symm)
      subst j
      rfl
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at he
      | succ j =>
        exact hh i j (by simpa using he) ((GorbowFreeSupportProof.unbindMembership _ i.val).mpr hi)

theorem encodingPreservation : Comparators.GorbowContextTransport.EncodingPreservation :=
  ⟨fun n m t u h => (termTransfer n t m u h).1,fun n m φ ψ h => (formulaTransfer n φ m ψ h).1⟩
theorem supportPreservation : Comparators.GorbowContextTransport.SupportPreservation :=
  ⟨fun n m t u h => (termTransfer n t m u h).2.1,fun n m φ ψ h => (formulaTransfer n φ m ψ h).2.1⟩
theorem semantics : Comparators.GorbowContextTransport.Semantics :=
  ⟨fun n m t u h => (termTransfer n t m u h).2.2,fun n m φ ψ h => (formulaTransfer n φ m ψ h).2.2⟩

private theorem rejection {α : Type} (o : Option α) (s : Finset Nat) (m : Nat)
    (h : (∃ a,o=some a) ↔ ∀ i∈s,i<m) : o=none ↔ ∃ i∈s,m≤i := by
  classical
  have hn : o=none ↔ ¬ ∃ a,o=some a := by cases o <;> simp
  rw [hn,h]
  simp only [not_forall,Nat.not_lt,exists_prop]

theorem exactRejection : Comparators.GorbowContextTransport.ExactRejection :=
  ⟨fun n m t => rejection _ _ _ (termDomain n t m),fun n m φ => rejection _ _ _ (formulaDomain n φ m)⟩

theorem namedClosure : Comparators.GorbowContextTransport.NamedClosure := by
  intro n v φ hs
  have hsa : formulaSupport (bindAll v φ)=∅ := by rw [(GorbowNamedBindingProof.bindingSupport n v φ).1,hs]; simp
  have hse : formulaSupport (bindEx v φ)=∅ := by rw [(GorbowNamedBindingProof.bindingSupport n v φ).2,hs]; simp
  obtain ⟨σ,hσ⟩ := (formulaDomain n (bindAll v φ) 0).mpr (by simp [hsa])
  obtain ⟨τ,hτ⟩ := (formulaDomain n (bindEx v φ) 0).mpr (by simp [hse])
  refine ⟨σ,τ,hσ,hτ,(encodingPreservation.2 _ _ _ _ hσ).symm,(encodingPreservation.2 _ _ _ _ hτ).symm,?_⟩
  intro I ρ
  have ha := semantics.2 n 0 (bindAll v φ) σ hσ I ρ Fin.elim0 (by intro i j; exact Fin.elim0 j)
  have he := semantics.2 n 0 (bindEx v φ) τ hτ I ρ Fin.elim0 (by intro i j; exact Fin.elim0 j)
  exact ⟨ha.symm.trans (GorbowNamedBindingProof.bindingSemantics n v φ I ρ).1,
    he.symm.trans (GorbowNamedBindingProof.bindingSemantics n v φ I ρ).2⟩

theorem gorbowContextTransport : Comparators.GorbowContextTransport.Target :=
  ⟨exactDomain,encodingPreservation,supportPreservation,semantics,exactRejection,namedClosure⟩
end LogicLineages.ComputabilityKnowledge.GorbowContextTransportProof
