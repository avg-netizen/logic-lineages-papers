module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorOmegaProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlgebraProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof

private theorem shift_exponent (e : ONote) (he : ONote.NF e) :
    (rawNaturalSum 1 e).repr=e.repr+1 := by
  have hd := naturalSumDenotation (⟨1,ONote.nf_one⟩ : NONote) (⟨e,he⟩ : NONote)
  change (rawNaturalSum 1 e).repr=ordinalNaturalSum (1 : ONote).repr e.repr at hd
  rw [hd,ONote.repr_one,sum_comm]
  simpa using actualNaturalSumFiniteRight e.repr 1

private def omegaShift : ONote → ONote
  | .zero => .zero
  | .oadd e c t => .oadd (rawNaturalSum 1 e) c (omegaShift t)

private theorem omegaShift_below : ∀ (t : ONote) (b : Ordinal), ONote.NFBelow t b →
    ONote.NFBelow (omegaShift t) (b+1)
  | .zero, _, _ => ONote.NFBelow.zero
  | .oadd e c t, b, ht => by
    apply ONote.NFBelow.oadd (rawNaturalSum_normal 1 e ONote.nf_one ht.fst)
    · simpa only [shift_exponent e ht.fst] using omegaShift_below t e.repr ht.snd
    · rw [shift_exponent e ht.fst,← Order.succ_eq_add_one,← Order.succ_eq_add_one]
      exact Order.succ_lt_succ ht.lt

private theorem omegaShift_normal (t : ONote) (ht : ONote.NF t) : ONote.NF (omegaShift t) := by
  cases t with
  | zero => exact ONote.NF.zero
  | oadd e c t =>
    apply ONote.NF.oadd (rawNaturalSum_normal 1 e ONote.nf_one ht.fst) c
    rw [shift_exponent e ht.fst]
    exact omegaShift_below t e.repr ht.snd'

private theorem singleton_merge (e : ONote) (c : ℕ+) (t : ONote)
    (he : ONote.NF e) (ht : ONote.NFBelow t e.repr) :
    rawNaturalSum (.oadd e c .zero) t=.oadd e c t := by
  cases t with
  | zero => simp only [rawNaturalSum]
  | oadd f d u =>
    have hcmp : ONote.cmp e f=.gt := (@ONote.cmp_compares e f he ht.fst).eq_gt.mpr ht.lt
    simp only [rawNaturalSum,hcmp]

private theorem monomial_shift : ∀ (t : ONote), ONote.NF t → rawMonomialProduct 1 1 t=omegaShift t
  | .zero, _ => rfl
  | .oadd e c t, ht => by
    simp only [rawMonomialProduct,monomial_shift t ht.snd,one_mul,omegaShift]
    apply singleton_merge
    · exact rawNaturalSum_normal 1 e ONote.nf_one ht.fst
    · rw [shift_exponent e ht.fst]
      exact omegaShift_below t e.repr ht.snd'

private theorem exponent_cmp (e f : ONote) (he : ONote.NF e) (hf : ONote.NF f) :
    ONote.cmp (rawNaturalSum 1 e) (rawNaturalSum 1 f)=ONote.cmp e f := by
  have hc := @ONote.cmp_compares e f he hf
  have hd := @ONote.cmp_compares (rawNaturalSum 1 e) (rawNaturalSum 1 f)
    (rawNaturalSum_normal 1 e ONote.nf_one he) (rawNaturalSum_normal 1 f ONote.nf_one hf)
  cases h : ONote.cmp e f with
  | lt =>
    apply hd.eq_lt.mpr
    change (rawNaturalSum 1 e).repr<(rawNaturalSum 1 f).repr
    rw [shift_exponent e he,shift_exponent f hf,← Order.succ_eq_add_one,← Order.succ_eq_add_one]
    exact Order.succ_lt_succ (hc.eq_lt.mp h)
  | eq =>
    have hef := ONote.eq_of_cmp_eq h
    subst f
    exact hd.eq_eq.mpr rfl
  | gt =>
    apply hd.eq_gt.mpr
    change (rawNaturalSum 1 f).repr<(rawNaturalSum 1 e).repr
    rw [shift_exponent f hf,shift_exponent e he,← Order.succ_eq_add_one,← Order.succ_eq_add_one]
    exact Order.succ_lt_succ (hc.eq_gt.mp h)

private theorem omegaShift_cmp : ∀ (a b : ONote), ONote.NF a → ONote.NF b →
    ONote.cmp (omegaShift a) (omegaShift b)=ONote.cmp a b
  | .zero, .zero, _, _ => rfl
  | .zero, .oadd _ _ _, _, _ => rfl
  | .oadd _ _ _, .zero, _, _ => rfl
  | .oadd e c t, .oadd f d u, ha, hb => by
    simp only [omegaShift,ONote.cmp,exponent_cmp e f ha.fst hb.fst,omegaShift_cmp t u ha.snd hb.snd]

private theorem omegaShift_value (t : NONote) :
    (omegaShift t.1).repr=ordinalNaturalProduct Ordinal.omega0 t.1.repr := by
  let w : NONote := ⟨.oadd 1 1 .zero,ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hw : w.1.repr=Ordinal.omega0 := by simp [w,ONote.repr]
  have hd := naturalProductDenotation w t
  change (rawNaturalProduct w.1 t.1).repr=_ at hd
  rw [hw] at hd
  have he : rawNaturalProduct w.1 t.1=omegaShift t.1 := by
    change rawNaturalSum (rawMonomialProduct 1 1 t.1) .zero=omegaShift t.1
    rw [monomial_shift t.1 t.2]
    cases h : omegaShift t.1 <;> simp only [rawNaturalSum]
  rwa [he] at hd

theorem omega_product_strict (h k : Ordinal) (he : h<epsilonZero) (ke : k<epsilonZero) (hk : h<k) :
    ordinalNaturalProduct Ordinal.omega0 h<ordinalNaturalProduct Ordinal.omega0 k := by
  obtain ⟨x,hx⟩ := normalRepresentationComplete h he
  obtain ⟨y,hy⟩ := normalRepresentationComplete k ke
  rw [← hx,← hy,← omegaShift_value x,← omegaShift_value y]
  have hc : ONote.cmp x.1 y.1=.lt := (@ONote.cmp_compares _ _ x.2 y.2).eq_lt.mpr (by simpa only [ONote.lt_def,hx,hy] using hk)
  exact (@ONote.cmp_compares _ _ (omegaShift_normal x.1 x.2) (omegaShift_normal y.1 y.2)).eq_lt.mp
    ((omegaShift_cmp x.1 y.1 x.2 y.2).trans hc)

theorem app_strict_head (h k : Ordinal) (s t q : Nat)
    (hh : 0<h) (he : h<epsilonZero) (ke : k<epsilonZero) (hk : h<k)
    (hn : actualOrdinalNorm h≤s) (hs : s≤q) (hq : 5≤q) :
    4*appValue h s q<appValue k t q :=
  app_head_domination h k s t q hh (hh.trans hk) he ke (omega_product_strict h k he ke hk) hn hs hq
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
