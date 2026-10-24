import R1Calculator.ForestWeights
import R1Calculator.ArithmeticLaws
import R1Calculator.CarlsonSupport

/-! Arithmetic extent of the concrete greedy forest placement. Induced
realization and lower bounds for arbitrary realizations are separate proofs. -/
namespace R1Calculator.OrderedForest.Forest

open Ordinal PureR1

/-- Greedy forest width equals the correction of its ordered normal weight.
Ordinal absorption is included through the genuine P-additivity theorem. -/
theorem width_repr_eq_principalSum : ∀ F : Forest,
    F.width.repr = (principalSum F.weight).repr
  | .nil => rfl
  | .cons c r => by
      haveI : ONote.NF c.weight := weight_nf c
      have hprincipal : ONote.NF (ONote.oadd c.weight 1 0) := inferInstance
      rw [width_cons_repr, width_repr_eq_principalSum c, width_repr_eq_principalSum r]
      rw [weight, principalSum_add_repr hprincipal (weight_nf r)]
      have hstep := principalSum_step_repr (1 : ℕ+) hprincipal
      have hh : Ordinal.omega0 ^ c.weight.repr + (principalSum c.weight).repr =
          (principalSum (ONote.oadd c.weight 1 0)).repr := by simpa using hstep.symm
      exact congrArg (fun x => x + (principalSum r.weight).repr) hh

theorem width_eq_principalSum (F : Forest) : F.width = principalSum F.weight := by
  haveI : ONote.NF F.width := width_nf F
  haveI : ONote.NF (principalSum F.weight) := principalSum_nf (weight_nf F)
  exact ONote.repr_inj.mp (width_repr_eq_principalSum F)

theorem finish_repr_eq (F : Forest) {σ : ONote} (hσ : ONote.NF σ) :
    (F.finish σ).repr = σ.repr + (principalSum F.weight).repr := by
  rw [finish_repr F hσ, width_repr_eq_principalSum]

/-- Exact endpoint of the first greedy root, including an arbitrary normal cut. -/
theorem greedy_root_endpoint (c : Forest) {σ : ONote} (hσ : ONote.NF σ) :
    (endpoint (σ + ONote.oadd c.weight 1 0)).repr =
      ((σ + ONote.oadd c.weight 1 0) + c.width).repr := by
  haveI : ONote.NF σ := hσ
  haveI : ONote.NF c.weight := weight_nf c
  haveI : ONote.NF c.width := width_nf c
  have hp : ONote.NF (ONote.oadd c.weight 1 0) := inferInstance
  rw [endpoint_add_right_repr hσ hp (by intro h; cases h),
    endpoint_principal_repr _ (weight_nf c), ONote.repr_add, ONote.repr_add,
    width_repr_eq_principalSum]
  exact (add_assoc _ _ _).symm

/-- Endpoints of ALL greedy labels are below the forest finish. This controls
negative relation atoms across different sibling blocks. -/
theorem label_endpoint_bounds : ∀ (F : Forest) {σ : ONote}, ONote.NF σ → ∀ i,
    (endpoint (F.label σ i)).repr ≤ (F.finish σ).repr
  | .nil, _, _, i => Fin.elim0 i
  | .cons c r, σ, hσ, i => by
      haveI : ONote.NF σ := hσ
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF c.width := width_nf c
      haveI : ONote.NF r.width := width_nf r
      let root := σ + ONote.oadd c.weight 1 0
      let cut := root + c.width
      have hrnf : ONote.NF root := ONote.add_nf _ _
      have hcnf : ONote.NF cut := ONote.add_nf _ _
      have hfin : ((Forest.cons c r).finish σ).repr = cut.repr + r.width.repr := by
        rw [finish_repr _ hσ, width_cons_repr]
        dsimp only [cut, root]
        rw [ONote.repr_add, ONote.repr_add]
        simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero, add_assoc]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [label_cons_root]
        rw [greedy_root_endpoint c hσ, hfin]
        exact le_self_add
      · refine Fin.addCases ?_ ?_ j
        · intro k
          simp only [label_cons_child]
          exact le_trans (label_endpoint_bounds c hrnf k)
            (show (c.finish root).repr ≤ ((Forest.cons c r).finish σ).repr by
              rw [hfin]; exact le_self_add)
        · intro k
          simp only [label_cons_rest]
          have h := label_endpoint_bounds r hcnf k
          simpa only [finish_repr r hcnf, hfin] using h

/-- Complete induced ordered-forest data, expressed recursively on its finite
preorder vertices. Both positive and negative cross-block atoms are required.
The diagonal atom also supplies the normal-notation witness for every point. -/
def Realizes : (F : Forest) → (Fin F.size → Ordinal.{0}) → Prop
  | .nil, _ => True
  | .cons c r, f =>
      let root := f (0 : Fin (c.size + r.size + 1))
      let fc := fun i : Fin c.size => f (Fin.castAdd r.size i).succ
      let fr := fun i : Fin r.size => f (Fin.natAdd c.size i).succ
      ArithmeticR1 root root ∧ Realizes c fc ∧ Realizes r fr ∧
      (∀ i, root < fc i ∧ ArithmeticR1 root (fc i)) ∧
      (∀ j, root < fr j ∧ ¬ ArithmeticR1 root (fr j)) ∧
      (∀ i j, fc i < fr j ∧ ¬ ArithmeticR1 (fc i) (fr j))

/-- Recursive full forest data preserve the preorder enumeration strictly. -/
theorem realizes_strictMono : ∀ (F : Forest) (f : Fin F.size → Ordinal.{0}),
    Realizes F f → StrictMono f
  | .nil, _, _ => fun i => Fin.elim0 i
  | .cons c r, f, hf => by
      rcases hf with ⟨_, hc, hr, hrootc, hrootr, hcr⟩
      have ihc := realizes_strictMono c _ hc
      have ihr := realizes_strictMono r _ hr
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · intro hij; exact (lt_irrefl _ hij).elim
        · refine Fin.addCases ?_ ?_ j
          · intro k _; exact (hrootc k).1
          · intro k _; exact (hrootr k).1
      · refine Fin.addCases ?_ ?_ i
        · intro ic j
          refine Fin.cases ?_ (fun j => ?_) j
          · intro hij
            change ic.val + 1 < 0 at hij
            omega
          · refine Fin.addCases ?_ ?_ j
            · intro jc hij
              apply ihc
              change ic.val + 1 < jc.val + 1 at hij
              change ic.val < jc.val
              omega
            · intro jr _; exact (hcr ic jr).1
        · intro ir j
          refine Fin.cases ?_ (fun j => ?_) j
          · intro hij
            change c.size + ir.val + 1 < 0 at hij
            omega
          · refine Fin.addCases ?_ ?_ j
            · intro jc hij
              change c.size + ir.val + 1 < jc.val + 1 at hij
              have hj := jc.isLt
              omega
            · intro jr hij
              apply ihr
              change c.size + ir.val + 1 < c.size + jr.val + 1 at hij
              change ir.val < jr.val
              omega

/-- Any two realizations of the SAME ordered forest agree on every
relation atom. This includes all negative and backward atoms, not only edges. -/
theorem realizes_rel_iff : ∀ (F : Forest) (f g : Fin F.size → Ordinal.{0}),
    Realizes F f → Realizes F g →
    ∀ i j, (ArithmeticR1 (f i) (f j) ↔ ArithmeticR1 (g i) (g j))
  | .nil, _, _, _, _ => fun i => Fin.elim0 i
  | .cons c r, f, g, hf, hg => by
      rcases hf with ⟨hff, hfc, hfr, hfrootc, hfrootr, hfcr⟩
      rcases hg with ⟨hgg, hgc, hgr, hgrootc, hgrootr, hgcr⟩
      have ihc := realizes_rel_iff c _ _ hfc hgc
      have ihr := realizes_rel_iff r _ _ hfr hgr
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact iff_of_true hff hgg
        · refine Fin.addCases ?_ ?_ j
          · intro jc; exact iff_of_true (hfrootc jc).2 (hgrootc jc).2
          · intro jr; exact iff_of_false (hfrootr jr).2 (hgrootr jr).2
      · refine Fin.addCases ?_ ?_ i
        · intro ic j
          refine Fin.cases ?_ (fun j => ?_) j
          · exact iff_of_false
              (fun h => (not_le_of_gt (hfrootc ic).1) (arithmeticR1_le h))
              (fun h => (not_le_of_gt (hgrootc ic).1) (arithmeticR1_le h))
          · refine Fin.addCases ?_ ?_ j
            · intro jc; exact ihc ic jc
            · intro jr; exact iff_of_false (hfcr ic jr).2 (hgcr ic jr).2
        · intro ir j
          refine Fin.cases ?_ (fun j => ?_) j
          · exact iff_of_false
              (fun h => (not_le_of_gt (hfrootr ir).1) (arithmeticR1_le h))
              (fun h => (not_le_of_gt (hgrootr ir).1) (arithmeticR1_le h))
          · refine Fin.addCases ?_ ?_ j
            · intro jc
              exact iff_of_false
                (fun h => (not_le_of_gt (hfcr jc ir).1) (arithmeticR1_le h))
                (fun h => (not_le_of_gt (hgcr jc ir).1) (arithmeticR1_le h))
            · intro jr; exact ihr ir jr

#print axioms realizes_rel_iff

private theorem endpoint_note_repr (a : NONote) :
    (endpointNF a).repr = a.repr + (principalSum (lastExponent a.val)).repr := by
  haveI : ONote.NF a.val := a.property
  haveI : ONote.NF (principalSum (lastExponent a.val)) :=
    principalSum_nf (lastExponent_nf a.property)
  exact ONote.repr_add _ _

private theorem weight_le_of_principalSum_le (c : Forest) (a : NONote)
    (h : (principalSum c.weight).repr ≤ (principalSum (lastExponent a.val)).repr) :
    c.weight.repr ≤ (lastExponent a.val).repr := by
  by_contra hn
  have hlt := principalSum_strictMono_repr (lastExponent_nf a.property) (weight_nf c)
    (lt_of_not_ge hn)
  exact (not_lt_of_ge h) hlt

/-- A cut-relative lower bound for EVERY actual arithmetic-candidate
realization, with arbitrary ordinal cut and upper bound. The explicit
cut<=bound premise pays the empty-forest case. -/
theorem minimum_bound : ∀ (F : Forest) (f : Fin F.size → Ordinal.{0})
    (cut bound : Ordinal.{0}), Realizes F f → cut ≤ bound →
    (∀ i, cut < f i) → (∀ i, f i ≤ bound) →
    cut + (principalSum F.weight).repr ≤ bound
  | .nil, _, _, _, _, h, _, _ => by simpa using h
  | .cons c r, f, cut, bound, hf, hcb, hcut, hupper => by
      rcases hf with ⟨hself, hc, hr, hrootc, hrootr, hcr⟩
      let i0 : Fin (c.size + r.size + 1) := 0
      let root := f i0
      let fc := fun i : Fin c.size => f (Fin.castAdd r.size i).succ
      let fr := fun i : Fin r.size => f (Fin.natAdd c.size i).succ
      obtain ⟨a, ha, _, _⟩ := hself
      have ha' : a.repr = root := ha
      have hb : root ≤ (endpointNF a).repr := by
        rw [← ha']; exact repr_le_endpoint a.property
      have hcend : ∀ i, fc i ≤ (endpointNF a).repr := by
        intro i
        exact ((arithmeticR1_note_iff a (fc i)).mp (ha'.symm ▸ (hrootc i).2)).2
      have hpc : root + (principalSum c.weight).repr ≤ (endpointNF a).repr :=
        minimum_bound c fc root (endpointNF a).repr hc hb (fun i => (hrootc i).1) hcend
      have hw : c.weight.repr ≤ (lastExponent a.val).repr := by
        apply weight_le_of_principalSum_le c a
        rw [endpoint_note_repr, ha'] at hpc
        exact (add_le_add_iff_left root).mp hpc
      have hrootmin : cut + ω ^ c.weight.repr ≤ root := by
        rw [← ha']
        have hca : cut < a.repr := by rw [ha']; exact hcut i0
        exact principal_rounding a.property hca hw
      have hstart : root + (principalSum c.weight).repr ≤ bound :=
        minimum_bound c fc root bound hc (hupper i0)
          (fun i => (hrootc i).1) (fun i => hupper (Fin.castAdd r.size i).succ)
      have hrstart : ∀ j, root + (principalSum c.weight).repr < fr j := by
        intro j
        have hn := (hrootr j).2
        have hrlt : (endpointNF a).repr < fr j := by
          by_contra hnot
          apply hn
          have hj : a.repr ≤ fr j := by
            simpa only [ha'] using (hrootr j).1.le
          have har : ArithmeticR1 a.repr (fr j) :=
            (arithmeticR1_note_iff a (fr j)).mpr ⟨hj, le_of_not_gt hnot⟩
          rw [ha'] at har
          exact har
        exact lt_of_le_of_lt hpc hrlt
      have hrest := minimum_bound r fr (root + (principalSum c.weight).repr) bound
        hr hstart hrstart (fun i => hupper (Fin.natAdd c.size i).succ)
      rw [← width_repr_eq_principalSum, width_cons_repr,
        width_repr_eq_principalSum c, width_repr_eq_principalSum r]
      have hh : (cut + ω ^ c.weight.repr) + (principalSum c.weight).repr +
          (principalSum r.weight).repr ≤ bound :=
        le_trans (add_le_add (add_le_add hrootmin le_rfl) le_rfl) hrest
      simpa only [add_assoc] using hh

/-- The child forest of a represented root cannot require more capacity
than its final Cantor exponent. The empty-child case is included. -/
theorem root_capacity (c : Forest) (a : NONote) (f : Fin c.size → Ordinal.{0})
    (hf : Realizes c f) (hroot : ∀ i, a.repr < f i ∧ ArithmeticR1 a.repr (f i)) :
    c.weight.repr ≤ (lastExponent a.val).repr := by
  have hc : a.repr + (principalSum c.weight).repr ≤ (endpointNF a).repr :=
    minimum_bound c f a.repr (endpointNF a).repr hf (repr_le_endpoint a.property)
      (fun i => (hroot i).1)
      (fun i => ((arithmeticR1_note_iff a (f i)).mp (hroot i).2).2)
  apply weight_le_of_principalSum_le c a
  rw [endpoint_note_repr] at hc
  exact (add_le_add_iff_left a.repr).mp hc

/-- The actual greedy labels realize the FULL induced forest, including
all negative cross-block atoms, for the arithmetic candidate relation. -/
theorem greedy_realizes : ∀ (F : Forest) {σ : ONote}, ONote.NF σ →
    Realizes F (fun i => (F.label σ i).repr)
  | .nil, _, _ => True.intro
  | .cons c r, σ, hσ => by
      haveI : ONote.NF σ := hσ
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF c.width := width_nf c
      let root := σ + ONote.oadd c.weight 1 0
      let cut := root + c.width
      have hrnf : ONote.NF root := ONote.add_nf _ _
      have hcnf : ONote.NF cut := ONote.add_nf _ _
      have hrc : root.repr ≤ cut.repr := by
        calc root.repr ≤ root.repr + c.width.repr := le_self_add
             _ = cut.repr := (ONote.repr_add root c.width).symm
      have hrootend : (endpoint root).repr = cut.repr := greedy_root_endpoint c hσ
      simp only [Realizes, label_cons_root, label_cons_child, label_cons_rest]
      refine ⟨arithmeticR1_note_refl ⟨root, hrnf⟩,
        greedy_realizes c hrnf, greedy_realizes r hcnf, ?_, ?_, ?_⟩
      · intro i
        have hb := label_bounds c hrnf i
        refine ⟨hb.1, (arithmeticR1_note_iff ⟨root, hrnf⟩ _).mpr ⟨hb.1.le, ?_⟩⟩
        change (c.label root i).repr ≤ (endpoint root).repr
        rw [hrootend]
        exact hb.2
      · intro j
        have hb := label_bounds r hcnf j
        refine ⟨lt_of_le_of_lt hrc hb.1, ?_⟩
        intro har
        have hu := ((arithmeticR1_note_iff ⟨root, hrnf⟩ _).mp har).2
        change (r.label cut j).repr ≤ (endpoint root).repr at hu
        rw [hrootend] at hu
        exact (not_le_of_gt hb.1) hu
      · intro i j
        have hc := (label_bounds c hrnf i).2
        have hr := (label_bounds r hcnf j).1
        refine ⟨lt_of_le_of_lt hc hr, ?_⟩
        intro har
        have hu := ((arithmeticR1_note_iff ⟨c.label root i, label_nf c hrnf i⟩ _).mp har).2
        change (r.label cut j).repr ≤ (endpoint (c.label root i)).repr at hu
        exact (not_le_of_gt hr) (le_trans hu (label_endpoint_bounds c hrnf i))

theorem greedy_strictMono (F : Forest) {σ : ONote} (hσ : ONote.NF σ) :
    StrictMono (fun i => (F.label σ i).repr) :=
  realizes_strictMono F _ (greedy_realizes F hσ)

/-- Extent includes the cut, so the empty forest has extent equal to its cut. -/
noncomputable def extent (F : Forest) (cut : Ordinal.{0}) (f : Fin F.size → Ordinal.{0}) : Ordinal.{0} :=
  max cut (Finset.univ.sup f)

theorem minimum_extent (F : Forest) (f : Fin F.size → Ordinal.{0}) (cut : Ordinal.{0})
    (hf : Realizes F f) (hcut : ∀ i, cut < f i) :
    cut + (principalSum F.weight).repr ≤ extent F cut f := by
  apply minimum_bound F f cut (extent F cut f) hf (le_max_left _ _) hcut
  intro i
  exact le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)

/-- The greedy realization ATTAINS the lower bound, not merely an upper
estimate. Thus the exact minimum extent after a normal cut is sigma+P(weight). -/
theorem greedy_extent_eq (F : Forest) {σ : ONote} (hσ : ONote.NF σ) :
    extent F σ.repr (fun i => (F.label σ i).repr) =
      σ.repr + (principalSum F.weight).repr := by
  apply le_antisymm
  · apply max_le
    · exact le_self_add
    · apply Finset.sup_le
      intro i _
      simpa only [finish_repr_eq F hσ] using (label_bounds F hσ i).2
  · exact minimum_extent F _ σ.repr (greedy_realizes F hσ)
      (fun i => (label_bounds F hσ i).1)

theorem extent_eq_sup (F : Forest) (cut : Ordinal.{0}) (f : Fin F.size → Ordinal.{0})
    (hne : 0 < F.size) (hcut : ∀ i, cut < f i) :
    extent F cut f = Finset.univ.sup f := by
  apply max_eq_right
  exact le_trans (hcut ⟨0, hne⟩).le (Finset.le_sup (Finset.mem_univ _))

/-- For nonempty forests the attained extent is literally the maximum label. -/
theorem greedy_maximum_eq (F : Forest) {σ : ONote} (hσ : ONote.NF σ)
    (hne : 0 < F.size) :
    Finset.univ.sup (fun i => (F.label σ i).repr) =
      σ.repr + (principalSum F.weight).repr := by
  rw [← extent_eq_sup F σ.repr _ hne (fun i => (label_bounds F hσ i).1)]
  exact greedy_extent_eq F hσ

/-- Strict translated-horizon capacity, including the empty forest.
The nonzero correction supplies room even when no labels are present. -/
theorem weight_lt_of_below_translated_principalSum (F : Forest) (cut : Ordinal.{0})
    (e : NONote) (he : e.val ≠ 0) (f : Fin F.size → Ordinal.{0})
    (hf : Realizes F f) (hcut : ∀ i, cut < f i)
    (hbelow : ∀ i, f i < cut + (principalSum e.val).repr) :
    F.weight.repr < e.repr := by
  have hpe := principalSum_repr_pos e.property he
  have htarget : cut < cut + (principalSum e.val).repr := lt_add_of_pos_right _ hpe
  have hpositive : (0 : Ordinal.{0}) < cut + (principalSum e.val).repr :=
    lt_of_le_of_lt bot_le htarget
  have hsup : Finset.univ.sup f < cut + (principalSum e.val).repr :=
    (Finset.sup_lt_iff hpositive).mpr (fun i _ => hbelow i)
  have hext : extent F cut f < cut + (principalSum e.val).repr := max_lt htarget hsup
  have hp : (principalSum F.weight).repr < (principalSum e.val).repr :=
    (add_lt_add_iff_left cut).mp
      (lt_of_le_of_lt (minimum_extent F f cut hf hcut) hext)
  have hm : StrictMono (fun a : NONote => (principalSum a.val).repr) := by
    intro a b hab
    exact principalSum_strictMono_repr a.property b.property hab
  change (⟨F.weight, weight_nf F⟩ : NONote) < e
  exact hm.lt_iff_lt.mp hp

/-- Zero-cut specialization; positivity of all labels remains explicit. -/
theorem weight_lt_of_below_principalSum (F : Forest) (e : NONote)
    (he : e.val ≠ 0) (f : Fin F.size → Ordinal.{0}) (hf : Realizes F f)
    (hpos : ∀ i, 0 < f i) (hbelow : ∀ i, f i < (principalSum e.val).repr) :
    F.weight.repr < e.repr := by
  apply weight_lt_of_below_translated_principalSum F 0 e he f hf hpos
  simpa only [zero_add] using hbelow

#print axioms weight_lt_of_below_translated_principalSum

#print axioms realizes_strictMono
#print axioms greedy_strictMono
#print axioms greedy_maximum_eq
#print axioms weight_lt_of_below_principalSum

#print axioms greedy_realizes
#print axioms greedy_extent_eq

#print axioms minimum_bound
#print axioms root_capacity

#print axioms width_repr_eq_principalSum
end R1Calculator.OrderedForest.Forest
