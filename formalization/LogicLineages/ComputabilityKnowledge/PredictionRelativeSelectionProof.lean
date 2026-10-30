module

public import LogicLineages.ComputabilityKnowledge.PredictionRelativeSelectionTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRelativeSelectionProof
open PredictionCanonicalList PredictionRelativeSelection PredictionRelativeSelectionTargets

private abbrev NC (f : Nat → Nat) : Prop :=
  Nat.RecursiveIn selectionOracles (fun n => Part.some (f n))

private theorem nc_prim {f : Nat → Nat} (hf : Primrec f) : NC f :=
  RecursiveIn.iff_nat.mp hf.computableIn

private theorem nc_comp {f g : Nat → Nat} (hf : NC f) (hg : NC g) : NC (fun n => f (g n)) :=
  (hf.comp hg).of_eq (fun _ => by simp)

private theorem nc_pair {f g : Nat → Nat} (hf : NC f) (hg : NC g) :
    NC (fun n => Nat.pair (f n) (g n)) :=
  (hf.pair hg).of_eq (fun _ => by simp [Seq.seq])

private theorem nc_binary {op : Nat → Nat → Nat} (hop : Primrec₂ op)
    {f g : Nat → Nat} (hf : NC f) (hg : NC g) : NC (fun n => op (f n) (g n)) := by
  have hp : NC (fun z : Nat => op z.unpair.1 z.unpair.2) :=
    nc_prim (hop.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
  exact (nc_comp hp (nc_pair hf hg)).of_eq (fun _ => by simp)

private theorem nc_prec {f g : Nat → Nat} (hf : NC f) (hg : NC g) :
    NC (fun z : Nat => Nat.rec (f z.unpair.1)
      (fun j v => g (Nat.pair z.unpair.1 (Nat.pair j v))) z.unpair.2) := by
  apply (hf.prec hg).of_eq
  intro z
  dsimp only
  generalize z.unpair = p
  rcases p with ⟨a, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
      dsimp only at ih
      simp only [Bind.bind] at ih ⊢
      simp only [Nat.rec_add_one, ih, Part.bind_some]

private theorem nc_total : NC totalIndicator :=
  Nat.RecursiveIn.oracle _ (by exact Or.inl rfl)
private theorem nc_equality : NC equalityIndicator :=
  Nat.RecursiveIn.oracle _ (by exact Or.inr rfl)

private noncomputable def earlierDifferent (i : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => earlierDifferent i n * (1 - equalityIndicator (Nat.pair n i))

private theorem earlier_rec (i n : Nat) :
    Nat.rec 1 (fun j v => v * (1 - equalityIndicator (Nat.pair j i))) n = earlierDifferent i n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [earlierDifferent, Nat.rec_add_one, ih]

private theorem earlier_formula (i n : Nat) :
    earlierDifferent i n = @ite Nat (∀ j < n, ¬ SameFunction (codeAt j) (codeAt i)) (Classical.propDecidable _) 1 0 := by
  classical
  induction n with
  | zero => simp [earlierDifferent]
  | succ n ih =>
      rw [earlierDifferent, ih]
      simp only [Nat.forall_lt_succ_right]
      by_cases h : ∀ j < n, ¬ SameFunction (codeAt j) (codeAt i)
      · by_cases hn : SameFunction (codeAt n) (codeAt i)
        · simp [equalityIndicator, Nat.unpair_pair, Nat.forall_lt_succ_right, h, hn]
        · simp [equalityIndicator, Nat.unpair_pair, Nat.forall_lt_succ_right, h, hn]
      · simp [equalityIndicator, Nat.unpair_pair, Nat.forall_lt_succ_right, h]

private theorem nc_earlier : NC (fun z : Nat => earlierDifferent z.unpair.1 z.unpair.2) := by
  have ha : NC (fun z : Nat => z.unpair.1) := nc_prim (Primrec.fst.comp Primrec.unpair)
  have hj : NC (fun z : Nat => z.unpair.2.unpair.1) :=
    nc_prim (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hv : NC (fun z : Nat => z.unpair.2.unpair.2) :=
    nc_prim (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have he := nc_comp nc_equality (nc_pair hj ha)
  have hs := nc_binary Primrec.nat_sub (nc_prim (Primrec.const 1)) he
  have hg := nc_binary Primrec.nat_mul hv hs
  apply (nc_prec (nc_prim (Primrec.const 1)) hg).of_eq
  intro z
  simpa only [Nat.unpair_pair] using congrArg Part.some (earlier_rec z.unpair.1 z.unpair.2)

theorem relativeRepresentativeDecision : RelativeRepresentativeDecision := by
  classical
  have he := nc_comp nc_earlier (nc_pair (nc_prim Primrec.id) (nc_prim Primrec.id))
  have hm := nc_binary Primrec.nat_mul nc_total he
  apply RecursiveIn.iff_nat.mpr
  apply hm.of_eq
  intro i
  simp only [Nat.unpair_pair]
  rw [earlier_formula]
  by_cases ht : TotalNat (codeAt i) <;>
    by_cases hd : ∀ j < i, ¬ SameFunction (codeAt j) (codeAt i) <;>
      simp [totalIndicator, representativeIndicator, Representative, ht, hd]

private theorem count_rec (n : Nat) :
    Nat.rec 0 (fun j v => v + representativeIndicator j) n = representativeCount n := by
  classical
  induction n with
  | zero => simp [representativeCount]
  | succ n ih =>
      change (Nat.rec 0 (fun j v => v + representativeIndicator j) n) + representativeIndicator n = representativeCount (n + 1)
      rw [ih]
      simp only [representativeCount, representativeIndicator, Nat.count_succ]

theorem relativeRepresentativeCounting : RelativeRepresentativeCounting := by
  have hr : NC representativeIndicator := RecursiveIn.iff_nat.mp relativeRepresentativeDecision
  have hj : NC (fun z : Nat => z.unpair.2.unpair.1) :=
    nc_prim (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hv : NC (fun z : Nat => z.unpair.2.unpair.2) :=
    nc_prim (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  have hg := nc_binary Primrec.nat_add hv (nc_comp hr hj)
  have hp := nc_prec (nc_prim (Primrec.const 0)) hg
  have hdiag := nc_comp hp (nc_pair (nc_prim (Primrec.const 0)) (nc_prim Primrec.id))
  apply RecursiveIn.iff_nat.mpr
  apply hdiag.of_eq
  intro n
  simpa only [Nat.unpair_pair, id_eq] using congrArg Part.some (count_rec n)

private noncomputable def searchTest (z : Nat) : Nat :=
  if representativeIndicator z.unpair.2 = 1 ∧ representativeCount z.unpair.2 = z.unpair.1 then 0 else 1

private theorem nc_search : NC searchTest := by
  have hi : NC (fun z : Nat => z.unpair.2) := nc_prim (Primrec.snd.comp Primrec.unpair)
  have hn : NC (fun z : Nat => z.unpair.1) := nc_prim (Primrec.fst.comp Primrec.unpair)
  have hr : NC representativeIndicator := RecursiveIn.iff_nat.mp relativeRepresentativeDecision
  have hc : NC representativeCount := RecursiveIn.iff_nat.mp relativeRepresentativeCounting
  have htuple := nc_pair (nc_comp hr hi) (nc_pair (nc_comp hc hi) hn)
  have htest : Primrec (fun z : Nat => if z.unpair.1 = 1 ∧ z.unpair.2.unpair.1 = z.unpair.2.unpair.2
      then (0 : Nat) else 1) :=
    Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1)).and
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))))
      (Primrec.const 0) (Primrec.const 1)
  exact (nc_comp (nc_prim htest) htuple).of_eq (fun z => by simp [searchTest])

private theorem search_zero (n i : Nat) : searchTest (Nat.pair n i) = 0 ↔
    Representative i ∧ representativeCount i = n := by
  classical
  simp [searchTest, representativeIndicator]

private theorem canonical_count (n : Nat) : representativeCount (canonicalIndex n) = n := by
  classical
  exact Nat.count_nth_of_infinite PredictionCanonicalListProof.infinitelyManyRepresentatives n

private theorem unique_search (n i : Nat) (hi : Representative i) (hc : representativeCount i = n) :
    i = canonicalIndex n := by
  classical
  have h := Nat.nth_count (p := Representative) hi
  change canonicalIndex (representativeCount i) = i at h
  rw [hc] at h
  exact h.symm

theorem relativeCanonicalSelection : RelativeCanonicalSelection := by
  apply RecursiveIn.iff_nat.mpr
  apply nc_search.rfind.of_eq
  intro n
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  constructor
  · have hz := (search_zero n (canonicalIndex n)).mpr
      ⟨PredictionCanonicalListProof.strictCanonicalEnumeration.2 n, canonical_count n⟩
    simp [hz]
  · intro i hi
    have hz : searchTest (Nat.pair n i) ≠ 0 := by
      intro h
      obtain ⟨hr, hc⟩ := (search_zero n i).mp h
      have he := unique_search n i hr hc
      omega
    simp [hz]

end LogicLineages.ComputabilityKnowledge.PredictionRelativeSelectionProof
