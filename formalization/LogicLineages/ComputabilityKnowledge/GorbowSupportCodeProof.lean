module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSupportCode
public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidationProof
public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
open GorbowSyntax GorbowSyntaxValidation GorbowFreeSupport GorbowSupportCode

private theorem termScan (n : Nat) (t : Term n) : ∀ (i : Fin n) (tasks : List Task) (b : Bool),
    (GorbowTermPrefixCode.encode t).foldl (observeStep (n-i.val)) (some ((0,n)::tasks),b) =
      (some tasks,b || t.uses i) := by
  induction t with
  | var j =>
      intro i tasks b
      have he : n - j.val = n - i.val ↔ i = j := by
        constructor
        · intro h; apply Fin.ext; omega
        · intro h; subst j; rfl
      simp [GorbowTermPrefixCode.encode, observeStep, sees, step, expand, j.isLt, he, Term.uses]
  | zero => intro i tasks b; simp [GorbowTermPrefixCode.encode, observeStep, sees, step, expand, Term.uses]
  | succ t ih | universalFunction t ih =>
      intro i tasks b
      simp [GorbowTermPrefixCode.encode, observeStep, sees, step, expand, ih, Term.uses]
  | add t u ht hu | mul t u ht hu =>
      intro i tasks b
      simp [GorbowTermPrefixCode.encode, List.foldl_append, observeStep, sees, step, expand, ht, hu, Term.uses, Bool.or_assoc]

private theorem formulaScan (n : Nat) (φ : Formula n) : ∀ (i : Fin n) (tasks : List Task) (b : Bool),
    (GorbowFormulaPrefixCode.encode φ).foldl (observeStep (n-i.val)) (some ((1,n)::tasks),b) =
      (some tasks,b || φ.uses i) := by
  induction φ with
  | equal t u | knowledge t u =>
      intro i tasks b
      simp [GorbowFormulaPrefixCode.encode, List.foldl_append, observeStep, sees, step, expand, termScan, Formula.uses, Bool.or_assoc]
  | universalRelation t | agent t | knowledgeAll t | truth t =>
      intro i tasks b
      simp [GorbowFormulaPrefixCode.encode, observeStep, sees, step, expand, termScan, Formula.uses]
  | neg φ ih =>
      intro i tasks b
      simp [GorbowFormulaPrefixCode.encode, observeStep, sees, step, expand, ih, Formula.uses]
  | imp φ ψ hφ hψ | conj φ ψ hφ hψ | disj φ ψ hφ hψ =>
      intro i tasks b
      simp [GorbowFormulaPrefixCode.encode, List.foldl_append, observeStep, sees, step, expand, hφ, hψ, Formula.uses, Bool.or_assoc]
  | all φ ih | ex φ ih =>
      intro i tasks b
      have h := ih i.succ tasks b
      simpa [GorbowFormulaPrefixCode.encode, observeStep, sees, step, expand, Formula.uses,
        Nat.add_sub_add_right] using h

theorem scannerInvariant : Comparators.GorbowSupportCode.ScannerInvariant := ⟨termScan, formulaScan⟩

private theorem termOccurs (n : Nat) (t : Term n) (i : Fin n) :
    occurs 0 n i.val (GorbowTermPrefixCode.encode t) = t.uses i := by
  simp only [occurs, i.isLt, ↓reduceIte, termScan, Bool.false_or]

private theorem formulaOccurs (n : Nat) (φ : Formula n) (i : Fin n) :
    occurs 1 n i.val (GorbowFormulaPrefixCode.encode φ) = φ.uses i := by
  simp only [occurs, i.isLt, ↓reduceIte, formulaScan, Bool.false_or]

private theorem validTermEncode (n : Nat) (t : Term n) : validTerm n (GorbowTermPrefixCode.encode t) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.1 n _).mpr
    ⟨t, (GorbowTermPrefixCodeProof.decoderExact n _ t).mpr rfl⟩

private theorem validFormulaEncode (n : Nat) (φ : Formula n) : validFormula n (GorbowFormulaPrefixCode.encode φ) = true :=
  (GorbowSyntaxValidationProof.exactTypedDomain.2 n _).mpr
    ⟨φ, (GorbowFormulaPrefixCodeProof.decoderExact n _ φ).mpr rfl⟩

private theorem termNamesEncode (n : Nat) (t : Term n) :
    termNames n (GorbowTermPrefixCode.encode t) =
      some ((List.range n).filter (fun i => decide (i ∈ termSupport t))) := by
  simp only [termNames, validTermEncode, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro i hi
  have hib := List.mem_range.mp hi
  rw [termOccurs n t ⟨i,hib⟩]
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using (GorbowFreeSupportProof.usesCalibration.1 n t ⟨i,hib⟩).symm)

private theorem formulaNamesEncode (n : Nat) (φ : Formula n) :
    formulaNames n (GorbowFormulaPrefixCode.encode φ) =
      some ((List.range n).filter (fun i => decide (i ∈ formulaSupport φ))) := by
  simp only [formulaNames, validFormulaEncode, ↓reduceIte]
  congr 1
  apply List.filter_congr
  intro i hi
  have hib := List.mem_range.mp hi
  rw [formulaOccurs n φ ⟨i,hib⟩]
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using (GorbowFreeSupportProof.usesCalibration.2 n φ ⟨i,hib⟩).symm)

theorem exactNames : Comparators.GorbowSupportCode.ExactNames := by
  constructor
  · intro n raw names
    constructor
    · intro h
      have hv : validTerm n raw = true := by
        by_contra hv
        simp [termNames, hv] at h
      obtain ⟨t, ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 n raw).mp hv
      have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp ht
      subst raw
      rw [termNamesEncode] at h
      exact ⟨t, rfl, (Option.some.inj h).symm⟩
    · rintro ⟨t, rfl, rfl⟩
      exact termNamesEncode n t
  · intro n raw names
    constructor
    · intro h
      have hv : validFormula n raw = true := by
        by_contra hv
        simp [formulaNames, hv] at h
      obtain ⟨φ, ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 n raw).mp hv
      have he := (GorbowFormulaPrefixCodeProof.decoderExact n raw φ).mp ht
      subst raw
      rw [formulaNamesEncode] at h
      exact ⟨φ, rfl, (Option.some.inj h).symm⟩
    · rintro ⟨φ, rfl, rfl⟩
      exact formulaNamesEncode n φ

theorem exactRejection : Comparators.GorbowSupportCode.ExactRejection := by
  constructor
  · intro n raw
    constructor
    · intro h
      cases hd : GorbowTermPrefixCode.decode n raw with
      | none => rfl
      | some t =>
          have he := (GorbowTermPrefixCodeProof.decoderExact n raw t).mp hd
          subst raw
          rw [termNamesEncode] at h
          cases h
    · intro hd
      have hv : validTerm n raw ≠ true := by
        intro h
        obtain ⟨t, ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.1 n raw).mp h
        rw [hd] at ht
        cases ht
      simp [termNames, hv]
  · intro n raw
    constructor
    · intro h
      cases hd : GorbowFormulaPrefixCode.decode n raw with
      | none => rfl
      | some φ =>
          have he := (GorbowFormulaPrefixCodeProof.decoderExact n raw φ).mp hd
          subst raw
          rw [formulaNamesEncode] at h
          cases h
    · intro hd
      have hv : validFormula n raw ≠ true := by
        intro h
        obtain ⟨φ, ht⟩ := (GorbowSyntaxValidationProof.exactTypedDomain.2 n raw).mp h
        rw [hd] at ht
        cases ht
      simp [formulaNames, hv]

private theorem filteredRangeSet (n : Nat) (s : Finset Nat) (hs : ∀ i ∈ s, i < n) :
    ((List.range n).filter (fun i => decide (i ∈ s))).toFinset = s := by
  ext i
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hs i h,h⟩⟩

private theorem filteredRangeCard (n : Nat) (s : Finset Nat) (hs : ∀ i ∈ s, i < n) :
    ((List.range n).filter (fun i => decide (i ∈ s))).length = s.card := by
  have h := List.toFinset_card_of_nodup ((List.nodup_range (n := n)).filter (fun i => decide (i ∈ s)))
  rw [filteredRangeSet n s hs] at h
  exact h.symm

theorem exactSelector : Comparators.GorbowSupportCode.ExactSelector := by
  intro raw
  simp only [selectorCode, decide_eq_true_eq]
  rw [exactNames.2]
  constructor
  · rintro ⟨φ, he, hn⟩
    have hs : formulaSupport φ = {0} := by
      have hset := filteredRangeSet 1 (formulaSupport φ) (GorbowFreeSupportProof.supportBound.2 1 φ)
      rw [← hn] at hset
      simpa using hset.symm
    have hu := (GorbowFreeSupportProof.selectorCalibration.1 φ).mpr hs
    exact ⟨⟨φ,hu⟩,he⟩
  · rintro ⟨A, he⟩
    refine ⟨A.val,he,?_⟩
    have hs := GorbowFreeSupportProof.selectorCalibration.2 A
    change formulaSupport A.val = {0} at hs
    simp [hs]

theorem exactPreciseArity : Comparators.GorbowSupportCode.ExactPreciseArity := by
  constructor
  · intro m n raw
    constructor
    · intro h
      cases hn : termNames m raw with
      | none => simp [preciseTermCode, hn] at h
      | some names =>
          obtain ⟨t, he, rfl⟩ := (exactNames.1 m raw names).mp hn
          have hc := filteredRangeCard m (termSupport t) (GorbowFreeSupportProof.supportBound.1 m t)
          exact ⟨t,he,by simpa [preciseTermCode, hn, hc] using h⟩
    · rintro ⟨t, rfl, ht⟩
      have hc := filteredRangeCard m (termSupport t) (GorbowFreeSupportProof.supportBound.1 m t)
      simp [preciseTermCode, termNamesEncode, hc, ht]
  · intro m n raw
    constructor
    · intro h
      cases hn : formulaNames m raw with
      | none => simp [preciseFormulaCode, hn] at h
      | some names =>
          obtain ⟨φ, he, rfl⟩ := (exactNames.2 m raw names).mp hn
          have hc := filteredRangeCard m (formulaSupport φ) (GorbowFreeSupportProof.supportBound.2 m φ)
          exact ⟨φ,he,by simpa [preciseFormulaCode, hn, hc, PreciselyFree] using h⟩
    · rintro ⟨φ, rfl, ht⟩
      have hc := filteredRangeCard m (formulaSupport φ) (GorbowFreeSupportProof.supportBound.2 m φ)
      simp [preciseFormulaCode, formulaNamesEncode, hc, show (formulaSupport φ).card = n from ht]
private theorem pr_seesList : Primrec (fun p : (Nat × Nat) × List Task =>
    match p.2 with
    | [] => false
    | task :: _ => decide (task.1 = 2 ∧ p.1.2 < task.2 ∧ task.2 - p.1.2 = p.1.1)) := by
  have hr : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hx : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hk : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun p : ((Nat × Nat) × List Task) × (Task × List Task) => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have h := Primrec.list_casesOn Primrec.snd (Primrec.const false)
    (((Primrec.eq.comp hk (Primrec.const 2)).and
      ((Primrec.nat_lt.comp hx hn).and (Primrec.eq.comp (Primrec.nat_sub.comp hn hx) hr))).decide.to₂)
  apply h.of_eq
  intro p
  cases p.2 <;> rfl

private theorem pr_sees : Primrec (fun p : Nat × State × Nat => sees p.1 p.2.1 p.2.2) := by
  have h := Primrec.option_casesOn (Primrec.fst.comp Primrec.snd : Primrec (fun p : Nat × State × Nat => p.2.1))
    (Primrec.const false)
    (pr_seesList.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd)).to₂
  apply h.of_eq
  intro p
  rcases p with ⟨rank,state,token⟩
  cases state with
  | none => rfl
  | some tasks => cases tasks <;> rfl

private theorem pr_observe : Primrec (fun p : Nat × ObservedState × Nat => observeStep p.1 p.2.1 p.2.2) := by
  have hs : Primrec (fun p : Nat × ObservedState × Nat => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hb : Primrec (fun p : Nat × ObservedState × Nat => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hx : Primrec (fun p : Nat × ObservedState × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact (GorbowSyntaxValidationProof.uniformPrograms.2.1.comp (hs.pair hx)).pair
    (Primrec.or.comp hb (pr_sees.comp (Primrec.fst.pair (hs.pair hx))))

private theorem pr_occurs : Primrec (fun p : Nat × Nat × Nat × List Nat => occurs p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hn : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hl : Primrec (fun p : Nat × Nat × Nat × List Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hr := Primrec.nat_sub.comp hn hi
  have hinit : Primrec (fun p : Nat × Nat × Nat × List Nat => (some [(p.1,p.2.1)],false)) :=
    (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.fst.pair hn) (Primrec.const []))).pair (Primrec.const false)
  have hfold := Primrec.list_foldl hl hinit (pr_observe.comp ((hr.comp Primrec.fst).pair Primrec.snd)).to₂
  exact Primrec.ite (Primrec.nat_lt.comp hi hn) (Primrec.snd.comp hfold) (Primrec.const false)

private theorem pr_filter {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).filter (p a)) := by
  have ht := Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
  have h := Primrec.list_foldr hf (Primrec.const []) ht.to₂
  exact h.of_eq (fun a => (List.filter_eq_foldr (p a) (f a)).symm)

private theorem pr_namesList (kind : Nat) : Primrec (fun p : Nat × List Nat =>
    (List.range p.1).filter (fun i => occurs kind p.1 i p.2)) := by
  have hp : Primrec (fun p : (Nat × List Nat) × Nat => occurs kind p.1.1 p.2 p.1.2) :=
    pr_occurs.comp ((Primrec.const kind).pair ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst))))
  exact pr_filter (Primrec.list_range.comp Primrec.fst) hp.to₂

private theorem pr_termNames : Primrec (fun p : Nat × List Nat => termNames p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp GorbowSyntaxValidationProof.uniformPrograms.2.2.2.1 (Primrec.const true))
    (Primrec.option_some.comp (pr_namesList 0)) (Primrec.const none)

private theorem pr_formulaNames : Primrec (fun p : Nat × List Nat => formulaNames p.1 p.2) :=
  Primrec.ite (Primrec.eq.comp GorbowSyntaxValidationProof.uniformPrograms.2.2.2.2 (Primrec.const true))
    (Primrec.option_some.comp (pr_namesList 1)) (Primrec.const none)

private theorem pr_selector : Primrec selectorCode :=
  (Primrec.eq.comp (pr_formulaNames.comp ((Primrec.const 1).pair Primrec.id)) (Primrec.const (some [0]))).decide

private theorem pr_anyLength {f : Nat × List Nat → Option (List Nat)} (hf : Primrec f) :
    Primrec (fun p : Nat × Nat × List Nat => (f (p.1,p.2.2)).any (fun names => decide (names.length = p.2.1))) := by
  have h := Primrec.option_casesOn (hf.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))
    (Primrec.const false)
    ((Primrec.eq.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).decide).to₂
  apply h.of_eq
  intro p
  cases f (p.1,p.2.2) <;> rfl

theorem uniformPrograms : Comparators.GorbowSupportCode.UniformPrograms :=
  ⟨pr_sees, pr_observe, pr_occurs, pr_termNames, pr_formulaNames, pr_selector,
    pr_anyLength pr_termNames, pr_anyLength pr_formulaNames⟩

theorem gorbowSupportCode : Comparators.GorbowSupportCode.Target :=
  ⟨scannerInvariant, exactNames, exactRejection, exactSelector, exactPreciseArity, uniformPrograms⟩
end LogicLineages.ComputabilityKnowledge.GorbowSupportCodeProof
