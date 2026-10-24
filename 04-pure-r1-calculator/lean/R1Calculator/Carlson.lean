import R1Calculator.CarlsonSupport
import R1Calculator.ForestCapacity
import R1Calculator.ForestExtraction
import R1Calculator.PrefixCut

/-!
# Constructive finite copies and obstructions for the endpoint characterization

Each hereditary notation gives an explicit finite ordered forest with the
same ordinal weight. Its canonical boundary tree supplies a finite induced
diagram that cannot reflect below the left endpoint. Conversely, finite
diagrams in the computed interval are copied cofinally below the left point,
fixing all old labels and preserving every positive and negative atom.

Both constructions concern the explicit arithmetic candidate and are proved
without a semantic characterization premise. Combined with the separately
constructed standalone semantics and its recursive uniqueness, they supply
the actual endpoint characterization in `Correctness.lean`.
-/

namespace R1Calculator
namespace OrderedForest

/-- Place `n` copies of one rooted tree before a forest. Coefficients are
expanded in this specification; this is not a binary-size complexity claim. -/
def repeatRoot (c : Forest) : Nat → Forest → Forest
  | 0, r => r
  | n + 1, r => .cons c (repeatRoot c n r)

theorem repeatRoot_weight_repr (c r : Forest) : ∀ n : Nat,
    (repeatRoot c n r).weight.repr =
      Ordinal.omega0 ^ c.weight.repr * (n : Nat) + r.weight.repr := by
  intro n
  induction n with
  | zero => simp [repeatRoot]
  | succ n ih =>
      rw [repeatRoot, Forest.weight_cons_repr, ih]
      have hn : n + 1 = 1 + n := Nat.add_comm n 1
      rw [hn]
      simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]

/-- Explicit finite forest for every raw hereditary notation. Its ordinal
weight is interpreted by genuine ordinal addition, not commutative sorting. -/
def canonicalForest : ONote → Forest
  | .zero => .nil
  | .oadd e n a => repeatRoot (canonicalForest e) (n : Nat) (canonicalForest a)

theorem canonicalForest_weight_repr : ∀ a : ONote,
    (canonicalForest a).weight.repr = a.repr
  | .zero => rfl
  | .oadd e n a => by
      rw [canonicalForest, repeatRoot_weight_repr,
        canonicalForest_weight_repr e, canonicalForest_weight_repr a]
      rfl

/-- For a normal input the canonical forest recovers the exact normal code. -/
theorem canonicalForest_weight {a : ONote} (ha : a.NF) :
    (canonicalForest a).weight = a := by
  haveI : a.NF := ha
  haveI : (canonicalForest a).weight.NF := Forest.weight_nf _
  exact ONote.repr_inj.mp (canonicalForest_weight_repr a)

/-- One root whose children encode the exponent. Its induced noncopy property
is proved below, rather than assumed in the finite syntax. -/
def canonicalBoundaryTree (a : ONote) : Forest :=
  .cons (canonicalForest a) .nil

theorem canonicalBoundaryTree_weight_repr (a : ONote) :
    (canonicalBoundaryTree a).weight.repr = Ordinal.omega0 ^ a.repr := by
  rw [canonicalBoundaryTree, Forest.weight_cons_repr, canonicalForest_weight_repr]
  simp

theorem canonicalBoundaryTree_size_pos (a : ONote) :
    0 < (canonicalBoundaryTree a).size := by
  simp [canonicalBoundaryTree, Forest.size]

def canonicalBoundaryRoot (a : ONote) : Fin (canonicalBoundaryTree a).size :=
  ⟨0, canonicalBoundaryTree_size_pos a⟩

theorem canonicalBoundary_label_root (a σ : ONote) :
    (canonicalBoundaryTree a).label σ (canonicalBoundaryRoot a) =
      σ + ONote.oadd (canonicalForest a).weight 1 0 := by
  have hi : canonicalBoundaryRoot a =
      (0 : Fin ((canonicalForest a).size + Forest.nil.size + 1)) := by
    apply Fin.ext
    simp [canonicalBoundaryRoot]
  rw [hi]
  exact Forest.label_cons_root _ _ _

theorem canonicalBoundary_finish_endpoint (a : ONote) {σ : ONote} (hσ : σ.NF) :
    ((canonicalBoundaryTree a).finish σ).repr =
      (endpoint (σ + ONote.oadd (canonicalForest a).weight 1 0)).repr := by
  let c := canonicalForest a
  haveI : σ.NF := hσ
  haveI : c.weight.NF := Forest.weight_nf c
  haveI : c.width.NF := Forest.width_nf c
  have he : ((canonicalBoundaryTree a).finish σ).repr =
      ((σ + ONote.oadd c.weight 1 0) + c.width).repr := by
    rw [Forest.finish_repr _ hσ]
    change σ.repr + (Forest.cons c .nil).width.repr = _
    rw [Forest.width_cons_repr]
    simp only [Forest.width_nil, ONote.repr_zero, add_zero,
      ONote.repr_add, ONote.repr, PNat.one_coe, Nat.cast_one, mul_one]
    exact (add_assoc _ _ _).symm
  exact he.trans (Forest.greedy_root_endpoint c hσ).symm

namespace Forest

/-- Full induced copies transport every recursively stated forest atom.
The relation here is the explicit arithmetic candidate; no semantic
elementarity theorem is supplied as a premise. -/
theorem Realizes.transport : ∀ (F : Forest) (f : Fin F.size → Ordinal.{0})
    (g : Ordinal.{0} → Ordinal.{0}), F.Realizes f →
    (∀ i j, g (f i) < g (f j) ↔ f i < f j) →
    (∀ i j, PureR1.ArithmeticR1 (g (f i)) (g (f j)) ↔
      PureR1.ArithmeticR1 (f i) (f j)) → F.Realizes (fun i => g (f i))
  | .nil, _, _, _, _, _ => trivial
  | .cons c r, f, g, hf, hlt, hrel => by
      rcases hf with ⟨hs, hc, hr, hrc, hrr, hcr⟩
      let i0 : Fin (c.size + r.size + 1) := 0
      refine ⟨(hrel i0 i0).mpr hs, ?_, ?_, ?_, ?_, ?_⟩
      · exact Realizes.transport c _ g hc
          (fun i j => hlt (Fin.castAdd r.size i).succ (Fin.castAdd r.size j).succ)
          (fun i j => hrel (Fin.castAdd r.size i).succ (Fin.castAdd r.size j).succ)
      · exact Realizes.transport r _ g hr
          (fun i j => hlt (Fin.natAdd c.size i).succ (Fin.natAdd c.size j).succ)
          (fun i j => hrel (Fin.natAdd c.size i).succ (Fin.natAdd c.size j).succ)
      · intro i
        exact ⟨(hlt i0 (Fin.castAdd r.size i).succ).mpr (hrc i).1,
          (hrel i0 (Fin.castAdd r.size i).succ).mpr (hrc i).2⟩
      · intro j
        exact ⟨(hlt i0 (Fin.natAdd c.size j).succ).mpr (hrr j).1,
          fun h => (hrr j).2 ((hrel i0 (Fin.natAdd c.size j).succ).mp h)⟩
      · intro i j
        exact ⟨(hlt (Fin.castAdd r.size i).succ (Fin.natAdd c.size j).succ).mpr (hcr i j).1,
          fun h => (hcr i j).2
            ((hrel (Fin.castAdd r.size i).succ (Fin.natAdd c.size j).succ).mp h)⟩

theorem Realizes.transport_of_preservesPattern (F : Forest)
    (f : Fin F.size → Ordinal.{0}) (g : Ordinal.{0} → Ordinal.{0})
    (hf : F.Realizes f) (X : Finset Ordinal.{0}) (hX : ∀ i, f i ∈ X)
    (hg : PureR1.PreservesPattern PureR1.ArithmeticR1 X g) :
    F.Realizes (fun i => g (f i)) :=
  Realizes.transport F f g hf
    (fun i j => hg.2.1 _ (hX i) _ (hX j))
    (fun i j => hg.2.2 _ (hX i) _ (hX j))

end Forest

/-- The canonical tree for the final exponent cannot have an induced copy
whose root is in the open final principal block. This is the noncopy core
of the endpoint obstruction; finite reflection is not an assumption. -/
theorem canonicalBoundaryTree_no_root_in_last_block (a : NONote) (ξ : Ordinal.{0})
    (ha : a.repr = ξ + Ordinal.omega0 ^ (lastExponent a.val).repr)
    (f : Fin (canonicalBoundaryTree (lastExponent a.val)).size → Ordinal.{0})
    (hf : Forest.Realizes (canonicalBoundaryTree (lastExponent a.val)) f)
    (hcut : ξ < f (canonicalBoundaryRoot (lastExponent a.val)))
    (hroot : f (canonicalBoundaryRoot (lastExponent a.val)) < a.repr) : False := by
  let c := canonicalForest (lastExponent a.val)
  let fc : Fin c.size → Ordinal.{0} := fun i => f (Fin.castAdd 0 i).succ
  rcases hf with ⟨hs, hc, _, hrc, _, _⟩
  obtain ⟨r, hr, _, _⟩ := hs
  have hi : (0 : Fin (c.size + Forest.nil.size + 1)) =
      canonicalBoundaryRoot (lastExponent a.val) := by
    apply Fin.ext
    simp [canonicalBoundaryRoot]
  have hr' : r.val.repr = f (canonicalBoundaryRoot (lastExponent a.val)) :=
    hr.trans (congrArg f hi)
  have hcapacity := Forest.root_capacity c r fc hc (fun i => by
    simpa only [hr, fc, Forest.size_nil] using hrc i)
  have he : (lastExponent a.val).repr ≤ (lastExponent r.val).repr := by
    rw [← canonicalForest_weight_repr (lastExponent a.val)]
    exact hcapacity
  have hcut' : ξ < r.repr := by
    change ξ < r.val.repr
    rw [hr']
    exact hcut
  have hminimum := principal_rounding r.property hcut' he
  have hlarge : a.repr ≤ f (canonicalBoundaryRoot (lastExponent a.val)) := by
    rw [ha]
    rw [← hr']
    exact hminimum
  exact (not_le_of_gt hroot) hlarge

/-- Above the computed endpoint there is an explicit finite diagram which
cannot reflect below the left point. Its labels are the canonical boundary
tree, with the last-block prefix fixed as an old parameter. This theorem
does NOT assume that the arithmetic candidate is semantic R1. -/
theorem arithmetic_not_finiteReflection_above (a : NONote) (β : Ordinal.{0})
    (hβ : (endpointNF a).repr < β) :
    ¬ PureR1.FiniteReflection PureR1.ArithmeticR1 a.repr β := by
  classical
  intro hreflect
  by_cases ha0 : a.val = 0
  · have ha : a.repr = 0 := by change a.val.repr = 0; rw [ha0]; rfl
    have he : (endpointNF a).repr = 0 := by
      change (endpoint a.val).repr = 0
      rw [ha0, endpoint_zero]
      rfl
    have hzero : (0 : Ordinal.{0}) < β := he ▸ hβ
    obtain ⟨f, hf, _, _⟩ := hreflect {0} (by
      intro x hx
      rcases Finset.mem_singleton.mp hx with rfl
      exact hzero)
    have hh := hf 0 (Finset.mem_singleton_self 0)
    rw [ha] at hh
    exact (not_lt_of_ge (bot_le : (0 : Ordinal.{0}) ≤ f 0)) hh
  obtain ⟨ξ, hξ, hsplit⟩ := PureR1.lastPrincipal_prefix a.property ha0
  obtain ⟨σ, hσ, hσξ⟩ := exists_nf_repr_of_lt a.property hξ
  let e := lastExponent a.val
  let T := canonicalBoundaryTree e
  let labels : Fin T.size → Ordinal.{0} := fun i => (T.label σ i).repr
  haveI : σ.NF := hσ
  haveI : (canonicalForest e).weight.NF := Forest.weight_nf _
  haveI : (σ + ONote.oadd (canonicalForest e).weight 1 0).NF := ONote.add_nf _ _
  haveI : a.val.NF := a.property
  have hrootrepr : (σ + ONote.oadd (canonicalForest e).weight 1 0).repr = a.repr := by
    rw [ONote.repr_add]
    simp only [ONote.repr, PNat.one_coe, Nat.cast_one, mul_one, add_zero,
      canonicalForest_weight_repr, hσξ]
    exact hsplit.symm
  have hrootnote : σ + ONote.oadd (canonicalForest e).weight 1 0 = a.val :=
    ONote.repr_inj.mp hrootrepr
  have hlabelroot : labels (canonicalBoundaryRoot e) = a.repr := by
    dsimp only [labels, T]
    rw [canonicalBoundary_label_root]
    exact hrootrepr
  have hfinish : (T.finish σ).repr = (endpointNF a).repr := by
    rw [canonicalBoundary_finish_endpoint e hσ, hrootnote]
    rfl
  let X : Finset Ordinal.{0} := insert ξ (Finset.univ.image labels)
  have hξmem : ξ ∈ X := Finset.mem_insert_self _ _
  have hmem : ∀ i, labels i ∈ X := fun i =>
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hX : ∀ x ∈ X, x < β := by
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact (hξ.trans_le (repr_le_endpoint a.property)).trans hβ
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ((Forest.label_bounds T hσ i).2.trans_eq hfinish).trans_lt hβ
  obtain ⟨f, hbelow, hfixed, hmap⟩ := hreflect X hX
  have hcopied : T.Realizes (fun i => f (labels i)) :=
    Forest.Realizes.transport_of_preservesPattern T labels f
      (Forest.greedy_realizes T hσ) X hmem hmap
  have hprefix : f ξ = ξ := hfixed ξ hξmem hξ
  have hrootcut : ξ < f (labels (canonicalBoundaryRoot e)) := by
    rw [← hprefix]
    exact (hmap.2.1 ξ hξmem _ (hmem _) ).mpr (hlabelroot ▸ hξ)
  exact canonicalBoundaryTree_no_root_in_last_block a ξ hsplit
    (fun i => f (labels i)) hcopied hrootcut (hbelow _ (hmem _))

/-- A finite induced forest strictly before the endpoint has weight smaller
than the left point's final principal block. The cut-relative capacity
theorem handles empty forests without an extra nonemptiness assumption. -/
theorem forest_weight_lt_last_principal (a : NONote) (ξ : Ordinal.{0})
    (hξ : ξ < a.repr)
    (hsplit : a.repr = ξ + Ordinal.omega0 ^ (lastExponent a.val).repr)
    (F : Forest) (f : Fin F.size → Ordinal.{0}) (hf : F.Realizes f)
    (hlower : ∀ i, a.repr ≤ f i) (hupper : ∀ i, f i < (endpointNF a).repr) :
    F.weight.repr < Ordinal.omega0 ^ (lastExponent a.val).repr := by
  let e := lastExponent a.val
  haveI : e.NF := lastExponent_nf a.property
  haveI : a.val.NF := a.property
  haveI : (principalSum e).NF := principalSum_nf (lastExponent_nf a.property)
  let p : NONote := ⟨ONote.oadd e 1 0, by infer_instance⟩
  have hp0 : p.val ≠ 0 := by intro h; cases h
  have hP : (principalSum p.val).repr =
      Ordinal.omega0 ^ e.repr + (principalSum e).repr := by
    have hs := principalSum_step_repr (e := e) (a := 0) (1 : ℕ+) (by infer_instance)
    simpa only [PNat.one_coe, Nat.cast_one, mul_one, principalSum_zero,
      ONote.repr_zero, add_zero] using hs
  have hH : (endpointNF a).repr = ξ + (principalSum p.val).repr := by
    change (endpoint a.val).repr = _
    rw [endpoint, ONote.repr_add]
    change a.repr + (principalSum e).repr = ξ + (principalSum p.val).repr
    rw [hsplit]
    exact (add_assoc _ _ _).trans (congrArg (fun z => ξ + z) hP.symm)
  have hw := Forest.weight_lt_of_below_translated_principalSum F ξ p hp0 f hf
    (fun i => hξ.trans_le (hlower i)) (fun i => by rw [← hH]; exact hupper i)
  simpa only [p, NONote.repr, ONote.repr, PNat.one_coe, Nat.cast_one,
    mul_one, ONote.repr_zero, add_zero] using hw

/-- Every actual finite diagram from the arithmetic interval has an induced
copy below its left endpoint, fixing all existing lower labels. The proof
constructs one common map, including all negative and mixed-prefix atoms. -/
theorem arithmetic_finiteReflection_of_interval (a : NONote) (β : Ordinal.{0})
    (hab : a.repr ≤ β) (hβ : β ≤ (endpointNF a).repr) :
    PureR1.FiniteReflection PureR1.ArithmeticR1 a.repr β := by
  classical
  by_cases heq : β = a.repr
  · subst β
    intro F hF
    exact ⟨id, hF, (fun _ _ _ => rfl),
      (fun _ _ _ _ => Iff.rfl), (fun _ _ _ _ => Iff.rfl),
      (fun _ _ _ _ => Iff.rfl)⟩
  have hproper : a.repr < β := lt_of_le_of_ne hab (Ne.symm heq)
  have ha0 : a.val ≠ 0 := by
    intro hz
    have ha : a.repr = 0 := by change a.val.repr = 0; rw [hz]; rfl
    have hend : (endpointNF a).repr = 0 := by
      change (endpoint a.val).repr = 0
      rw [hz, endpoint_zero]
      rfl
    exact (not_lt_of_ge (hend ▸ hβ)) (ha ▸ hproper)
  obtain ⟨ξ, hξ, hsplit⟩ := PureR1.lastPrincipal_prefix a.property ha0
  change ξ < a.repr at hξ
  change a.repr = ξ + Ordinal.omega0 ^ (lastExponent a.val).repr at hsplit
  have hapos : 0 < a.repr := lt_of_le_of_lt bot_le hξ
  have har : PureR1.ArithmeticR1 a.repr β :=
    (PureR1.arithmeticR1_note_iff a β).mpr ⟨hab, hβ⟩
  intro F hF
  let X := F.filter (fun x => x < a.repr)
  let Y := F.filter (fun x => a.repr ≤ x)
  have hX : ∀ x ∈ X, x < a.repr := fun _ hx => (Finset.mem_filter.mp hx).2
  have hXF : ∀ x ∈ X, x ∈ F := fun _ hx => (Finset.mem_filter.mp hx).1
  have hYF : ∀ x ∈ Y, x ∈ F := fun _ hx => (Finset.mem_filter.mp hx).1
  have hY : ∀ x ∈ Y, a.repr ≤ x := fun _ hx => (Finset.mem_filter.mp hx).2
  have oldmem {x : Ordinal.{0}} (hx : x ∈ F) (hxa : x < a.repr) : x ∈ X :=
    Finset.mem_filter.mpr ⟨hx, hxa⟩
  have newmem {x : Ordinal.{0}} (hx : x ∈ F) (hxa : ¬ x < a.repr) : x ∈ Y :=
    Finset.mem_filter.mpr ⟨hx, le_of_not_gt hxa⟩
  obtain ⟨T, hcard, hv⟩ := Forest.extract_finset_below (endpointNF a) Y
    (fun x hx => (hF x (hYF x hx)).le.trans hβ)
  let v : Fin T.size → Ordinal.{0} := Y.orderEmbOfFin hcard
  have hvmem : ∀ i, v i ∈ Y := fun i => Y.orderEmbOfFin_mem hcard i
  have hvlo : ∀ i, a.repr ≤ v i := fun i => hY _ (hvmem i)
  have hvhi : ∀ i, v i < (endpointNF a).repr :=
    fun i => (hF _ (hYF _ (hvmem i))).trans_le hβ
  have hw := forest_weight_lt_last_principal a ξ hξ hsplit T v hv hvlo hvhi
  obtain ⟨cut, hcut, hXcut, hcross⟩ :=
    PureR1.arithmeticR1_finite_anchor_cut a hapos X hX
  obtain ⟨σ, hσ, hσcut⟩ := exists_nf_repr_of_lt a.property hcut
  let z : Fin T.size → Ordinal.{0} := fun i => (T.label σ i).repr
  have hzR : T.Realizes z := Forest.greedy_realizes T hσ
  have hwidth : T.width.repr < Ordinal.omega0 ^ (lastExponent a.val).repr := by
    rw [Forest.width_repr_eq_principalSum]
    exact principalSum_lt_principal_bound (Forest.weight_nf T) hw
  have hfinish : (T.finish σ).repr < a.repr := by
    rw [Forest.finish_repr T hσ, hsplit]
    apply add_small_lt_final_block
    · rw [← hsplit, hσcut]
      exact hcut
    · exact hwidth
  have hzlo : ∀ i, cut < z i := fun i => by
    rw [← hσcut]
    exact (Forest.label_bounds T hσ i).1
  have hzhi : ∀ i, z i < a.repr :=
    fun i => ((Forest.label_bounds T hσ i).2).trans_lt hfinish
  have hzmono : StrictMono z := Forest.greedy_strictMono T hσ
  have hvmono : StrictMono v := (Y.orderEmbOfFin hcard).strictMono
  have hrel := Forest.realizes_rel_iff T z v hzR hv
  let idx : (x : Ordinal.{0}) → x ∈ Y → Fin T.size :=
    fun x hx => (Y.orderIsoOfFin hcard).symm ⟨x, hx⟩
  have hidx (x : Ordinal.{0}) (hx : x ∈ Y) : v (idx x hx) = x :=
    congrArg Subtype.val ((Y.orderIsoOfFin hcard).apply_symm_apply ⟨x, hx⟩)
  let g : Ordinal.{0} → Ordinal.{0} :=
    fun x => if hx : x ∈ Y then z (idx x hx) else x
  have gold {x : Ordinal.{0}} (hx : x ∈ X) : g x = x := by
    have hn : x ∉ Y := fun hy => (not_le_of_gt (hX x hx)) (hY x hy)
    simp only [g, dif_neg hn]
  have gnew {x : Ordinal.{0}} (hx : x ∈ Y) : g x = z (idx x hx) := by
    simp only [g, dif_pos hx]
  have gnewlo {x : Ordinal.{0}} (hx : x ∈ Y) : cut < g x := by
    rw [gnew hx]
    exact hzlo _
  have gnewhi {x : Ordinal.{0}} (hx : x ∈ Y) : g x < a.repr := by
    rw [gnew hx]
    exact hzhi _
  have mixed_order {x y : Ordinal.{0}} (hx : x ∈ X) (hy : y ∈ Y) :
      x < y ∧ g x < g y := by
    refine ⟨(hX x hx).trans_le (hY y hy), ?_⟩
    rw [gold hx]
    exact lt_of_le_of_lt (hXcut x hx) (gnewlo hy)
  have mixed_rel {x y : Ordinal.{0}} (hx : x ∈ X) (hy : y ∈ Y) :
      PureR1.ArithmeticR1 (g x) (g y) ↔ PureR1.ArithmeticR1 x y := by
    rw [gold hx]
    exact (hcross x hx (g y) (gnewlo hy) (gnewhi hy)).trans
      (PureR1.arithmeticR1_cross_cut har (hX x hx).le (hY y hy)
        (hF y (hYF y hy)).le).symm
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxa : x < a.repr
    · rw [gold (oldmem hx hxa)]
      exact hxa
    · exact gnewhi (newmem hx hxa)
  · intro x hx hxa
    exact gold (oldmem hx hxa)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    by_cases hxa : x < a.repr
    · by_cases hya : y < a.repr
      · simp only [gold (oldmem hx hxa), gold (oldmem hy hya)]
      · have hm := mixed_order (oldmem hx hxa) (newmem hy hya)
        exact iff_of_false (ne_of_lt hm.2) (ne_of_lt hm.1)
    · by_cases hya : y < a.repr
      · have hm := mixed_order (oldmem hy hya) (newmem hx hxa)
        exact iff_of_false (ne_of_gt hm.2) (ne_of_gt hm.1)
      · let ix := idx x (newmem hx hxa)
        let iy := idx y (newmem hy hya)
        rw [gnew (newmem hx hxa), gnew (newmem hy hya)]
        exact hzmono.injective.eq_iff.trans
          (hvmono.injective.eq_iff.symm.trans (by rw [hidx, hidx]))
  · intro x hx y hy
    by_cases hxa : x < a.repr
    · by_cases hya : y < a.repr
      · simp only [gold (oldmem hx hxa), gold (oldmem hy hya)]
      · have hm := mixed_order (oldmem hx hxa) (newmem hy hya)
        exact iff_of_true hm.2 hm.1
    · by_cases hya : y < a.repr
      · have hm := mixed_order (oldmem hy hya) (newmem hx hxa)
        exact iff_of_false (not_lt_of_ge hm.2.le) (not_lt_of_ge hm.1.le)
      · rw [gnew (newmem hx hxa), gnew (newmem hy hya)]
        exact hzmono.lt_iff_lt.trans (hvmono.lt_iff_lt.symm.trans (by rw [hidx, hidx]))
  · intro x hx y hy
    by_cases hxa : x < a.repr
    · by_cases hya : y < a.repr
      · simp only [gold (oldmem hx hxa), gold (oldmem hy hya)]
      · exact mixed_rel (oldmem hx hxa) (newmem hy hya)
    · by_cases hya : y < a.repr
      · have hm := mixed_order (oldmem hy hya) (newmem hx hxa)
        exact iff_of_false
          (fun h => (not_le_of_gt hm.2) (PureR1.arithmeticR1_le h))
          (fun h => (not_le_of_gt hm.1) (PureR1.arithmeticR1_le h))
      · rw [gnew (newmem hx hxa), gnew (newmem hy hya)]
        simpa only [hidx] using hrel (idx x (newmem hx hxa)) (idx y (newmem hy hya))

example : (canonicalForest 2).size = 2 := by decide
example : (canonicalBoundaryTree 2).size = 3 := by decide
example : (canonicalBoundaryTree ONote.omega).size = 3 := by decide

#print axioms canonicalForest_weight_repr
#print axioms canonicalForest_weight
#print axioms canonicalBoundaryTree_weight_repr
#print axioms Forest.Realizes.transport
#print axioms canonicalBoundaryTree_no_root_in_last_block
#print axioms arithmetic_not_finiteReflection_above
#print axioms forest_weight_lt_last_principal
#print axioms arithmetic_finiteReflection_of_interval

end OrderedForest
end R1Calculator
