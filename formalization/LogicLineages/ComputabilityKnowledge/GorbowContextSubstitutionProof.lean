module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowContextSubstitution
public import LogicLineages.ComputabilityKnowledge.GorbowContextTransportProof
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCodeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowContextSubstitutionProof
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding GorbowFormulaSubstitution GorbowContextTransport
open GorbowContextSubstitution GorbowTermShiftCode

private theorem mapSome {α β : Type} (f : α → β) (o : Option α) (b : β) :
    o.map f=some b ↔ ∃ a, o=some a ∧ f a=b := by cases o <;> simp
private theorem twoSome {α β γ : Type} (f : α → β → γ) (o : Option α) (p : Option β) (c : γ) :
    (do let a ← o; let b ← p; pure (f a b))=some c ↔ ∃ a b, o=some a ∧ p=some b ∧ f a b=c := by
  cases o <;> cases p <;> simp

theorem shiftTransport : Comparators.GorbowContextSubstitution.ShiftTransport := by
  intro n m b t
  induction t generalizing m with
  | var i =>
    intro u h
    by_cases hv : i.val<m
    · have he : Term.var (⟨i.val,hv⟩ : Fin m)=u := by simpa [term,hv] using h
      subst u
      simp [shiftTerm,renameTerm,GorbowSubstitution.substitute,shiftVar,term,Nat.add_lt_add_right hv b]
    · simp [term,hv] at h
  | zero =>
    intro u h
    have he : Term.zero=u := by simpa [term] using h
    subst u
    rfl
  | succ t ih =>
    intro u h
    obtain ⟨a,ha,he⟩ := (mapSome Term.succ (term m t) u).mp h
    subst u
    change (term (m+b) (shiftTerm b t)).map Term.succ=some (Term.succ (shiftTerm b a))
    rw [ih m a ha]
    rfl
  | universalFunction t ih =>
    intro u h
    obtain ⟨a,ha,he⟩ := (mapSome Term.universalFunction (term m t) u).mp h
    subst u
    change (term (m+b) (shiftTerm b t)).map Term.universalFunction=some (Term.universalFunction (shiftTerm b a))
    rw [ih m a ha]
    rfl
  | add t u ht hu =>
    intro w h
    obtain ⟨a,c,ha,hc,he⟩ := (twoSome Term.add (term m t) (term m u) w).mp h
    subst w
    change (do let t' ← term (m+b) (shiftTerm b t); let u' ← term (m+b) (shiftTerm b u); pure (Term.add t' u'))=some (Term.add (shiftTerm b a) (shiftTerm b c))
    rw [ht m a ha,hu m c hc]
    rfl
  | mul t u ht hu =>
    intro w h
    obtain ⟨a,c,ha,hc,he⟩ := (twoSome Term.mul (term m t) (term m u) w).mp h
    subst w
    change (do let t' ← term (m+b) (shiftTerm b t); let u' ← term (m+b) (shiftTerm b u); pure (Term.mul t' u'))=some (Term.mul (shiftTerm b a) (shiftTerm b c))
    rw [ht m a ha,hu m c hc]
    rfl

private theorem shiftOne (n : Nat) : shiftVar n 1=Fin.succ := by
  funext i
  exact Fin.ext rfl

theorem liftCompatibility : Comparators.GorbowContextSubstitution.LiftCompatibility := by
  intro n m k l φ ψ hφ σ τ h i j he hi
  cases i using Fin.cases with
  | zero =>
    have hj : j=0 := Fin.ext (by simpa using he.symm)
    subst j
    simp [liftSubstitute,term]
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at he
    | succ j =>
      have hh := h i j (by simpa using he) ((GorbowFreeSupportProof.unbindMembership _ i.val).mpr hi)
      have hs := shiftTransport k l 1 (σ i) (τ j) hh
      simpa [liftSubstitute,shiftTerm,shiftOne] using hs

private theorem termSub (n : Nat) (t : Term n) : ∀ m k l (u : Term m), term m t=some u →
    ∀ (σ : Fin n → Term k) (τ : Fin m → Term l), Compatible (termSupport t) σ τ →
    term l (GorbowSubstitution.substitute σ t)=some (GorbowSubstitution.substitute τ u) := by
  induction t with
  | var i =>
    intro m k l u h σ τ hc
    by_cases hv : i.val<m
    · have he : Term.var (⟨i.val,hv⟩ : Fin m)=u := by simpa [term,hv] using h
      subst u
      exact hc i ⟨i.val,hv⟩ rfl (by simp [termSupport])
    · simp [term,hv] at h
  | zero =>
    intro m k l u h σ τ hc
    have he : Term.zero=u := by simpa [term] using h
    subst u
    rfl
  | succ t ih =>
    intro m k l u h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Term.succ (term m t) u).mp h
    subst u
    simp only [GorbowSubstitution.substitute,term,ih m k l a ha σ τ hc,Option.map_some]
  | universalFunction t ih =>
    intro m k l u h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Term.universalFunction (term m t) u).mp h
    subst u
    simp only [GorbowSubstitution.substitute,term,ih m k l a ha σ τ hc,Option.map_some]
  | add t u ht hu =>
    intro m k l w h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Term.add (term m t) (term m u) w).mp h
    subst w
    have ea := ht m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := hu m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [GorbowSubstitution.substitute,term,ea,eb]
  | mul t u ht hu =>
    intro m k l w h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Term.mul (term m t) (term m u) w).mp h
    subst w
    have ea := ht m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := hu m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [GorbowSubstitution.substitute,term,ea,eb]

theorem termSubstitution : Comparators.GorbowContextSubstitution.TermSubstitution :=
  fun n m k l t u h σ τ hc => termSub n t m k l u h σ τ hc

private theorem formulaSub (n : Nat) (φ : Formula n) : ∀ m k l (ψ : Formula m), formula m φ=some ψ →
    ∀ (σ : Fin n → Term k) (τ : Fin m → Term l), Compatible (formulaSupport φ) σ τ →
    formula l (substituteFormula σ φ)=some (substituteFormula τ ψ) := by
  induction φ with
  | equal t u =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.equal (term m t) (term m u) ψ).mp h
    subst ψ
    have ea := termSub _ t m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := termSub _ u m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [substituteFormula,formula,ea,eb]
  | knowledge t u =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.knowledge (term m t) (term m u) ψ).mp h
    subst ψ
    have ea := termSub _ t m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := termSub _ u m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [substituteFormula,formula,ea,eb]
  | universalRelation t =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.universalRelation (term m t) ψ).mp h
    subst ψ
    simp only [substituteFormula,formula,termSub _ t m k l a ha σ τ hc,Option.map_some]
  | agent t =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.agent (term m t) ψ).mp h
    subst ψ
    simp only [substituteFormula,formula,termSub _ t m k l a ha σ τ hc,Option.map_some]
  | knowledgeAll t =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.knowledgeAll (term m t) ψ).mp h
    subst ψ
    simp only [substituteFormula,formula,termSub _ t m k l a ha σ τ hc,Option.map_some]
  | truth t =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.truth (term m t) ψ).mp h
    subst ψ
    simp only [substituteFormula,formula,termSub _ t m k l a ha σ τ hc,Option.map_some]
  | neg φ ih =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.neg (formula m φ) ψ).mp h
    subst ψ
    simp only [substituteFormula,formula,ih m k l a ha σ τ hc,Option.map_some]
  | imp φ ψ hφ hψ =>
    intro m k l χ h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.imp (formula m φ) (formula m ψ) χ).mp h
    subst χ
    have ea := hφ m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := hψ m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [substituteFormula,formula,ea,eb]
  | conj φ ψ hφ hψ =>
    intro m k l χ h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.conj (formula m φ) (formula m ψ) χ).mp h
    subst χ
    have ea := hφ m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := hψ m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [substituteFormula,formula,ea,eb]
  | disj φ ψ hφ hψ =>
    intro m k l χ h σ τ hc
    obtain ⟨a,b,ha,hb,he⟩ := (twoSome Formula.disj (formula m φ) (formula m ψ) χ).mp h
    subst χ
    have ea := hφ m k l a ha σ τ (fun i j he hi => hc i j he (Finset.mem_union_left _ hi))
    have eb := hψ m k l b hb σ τ (fun i j he hi => hc i j he (Finset.mem_union_right _ hi))
    simp [substituteFormula,formula,ea,eb]
  | all φ ih =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.all (formula (m+1) φ) ψ).mp h
    subst ψ
    have hl := liftCompatibility _ m k l φ a ha σ τ hc
    have hb := ih (m+1) (k+1) (l+1) a ha (liftSubstitute σ) (liftSubstitute τ) hl
    simp only [substituteFormula,formula,hb,Option.map_some]
  | ex φ ih =>
    intro m k l ψ h σ τ hc
    obtain ⟨a,ha,he⟩ := (mapSome Formula.ex (formula (m+1) φ) ψ).mp h
    subst ψ
    have hl := liftCompatibility _ m k l φ a ha σ τ hc
    have hb := ih (m+1) (k+1) (l+1) a ha (liftSubstitute σ) (liftSubstitute τ) hl
    simp only [substituteFormula,formula,hb,Option.map_some]

theorem formulaSubstitution : Comparators.GorbowContextSubstitution.FormulaSubstitution :=
  fun n m k l φ ψ h σ τ hc => formulaSub n φ m k l ψ h σ τ hc

private theorem bindCompatible (n m : Nat) (v : Fin n) (w : Fin m) (hv : v.val=w.val) (support : Finset Nat) :
    Compatible support (bindDictionary v) (bindDictionary w) := by
  intro i j he hi
  have heq : i=v ↔ j=w := by
    constructor <;> intro h
    · subst i; exact Fin.ext (he.symm.trans hv)
    · subst j; exact Fin.ext (he.trans hv.symm)
  by_cases h : i=v
  · have hj := heq.mp h
    simp [bindDictionary,h,hj,term]
  · have hj : j≠w := fun hj => h (heq.mpr hj)
    simp [bindDictionary,h,hj,term,he,j.isLt,Fin.ext_iff]
private theorem selectCompatible (n m : Nat) (v : Fin n) (w : Fin m) (hv : v.val=w.val) (support : Finset Nat) :
    Compatible support (selectDictionary v) (selectDictionary w) := by
  intro i j he hi
  have heq : i=v ↔ j=w := by
    constructor <;> intro h
    · subst i; exact Fin.ext (he.symm.trans hv)
    · subst j; exact Fin.ext (he.trans hv.symm)
  by_cases h : i=v
  · have hj := heq.mp h
    simp [selectDictionary,h,hj,term]
  · have hj : j≠w := fun hj => h (heq.mpr hj)
    simp [selectDictionary,h,hj,term]

theorem namedCommutation : Comparators.GorbowContextSubstitution.NamedCommutation := by
  intro n m v w hv φ ψ h
  have hb := formulaSubstitution n m (n+1) (m+1) φ ψ h (bindDictionary v) (bindDictionary w) (bindCompatible n m v w hv _)
  have hs := formulaSubstitution n m 1 1 φ ψ h (selectDictionary v) (selectDictionary w) (selectCompatible n m v w hv _)
  refine ⟨by simp [bindAll,formula,hb],by simp [bindEx,formula,hb],?_⟩
  apply GorbowFormulaPrefixCodeProof.encodingInjective 1
  exact GorbowContextTransportProof.encodingPreservation.2 1 1 _ _ hs

theorem namedEncoding : Comparators.GorbowContextSubstitution.NamedEncoding := by
  intro n m v w hv φ ψ h
  obtain ⟨ha,he,hs⟩ := namedCommutation n m v w hv φ ψ h
  exact ⟨GorbowContextTransportProof.encodingPreservation.2 _ _ _ _ ha,
    GorbowContextTransportProof.encodingPreservation.2 _ _ _ _ he,congrArg GorbowFormulaPrefixCode.encode hs⟩

theorem gorbowContextSubstitution : Comparators.GorbowContextSubstitution.Target :=
  ⟨shiftTransport,liftCompatibility,termSubstitution,formulaSubstitution,namedCommutation,namedEncoding⟩
end LogicLineages.ComputabilityKnowledge.GorbowContextSubstitutionProof
