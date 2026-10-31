module
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductTargets
public import LogicLineages.OrdinalComparison.NaturalProductInterpretation
public import LogicLineages.OrdinalComparison.OrdinalRepresentationComplete

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

private theorem head_le_sum (e : ONote) (c : ℕ+) (t b : ONote)
    (he : ONote.NF e) (hb : ONote.NF b) :
    Ordinal.omega0 ^ e.repr ≤ (rawNaturalSum (.oadd e c t) b).repr := by
  cases b with
  | zero => simpa only [rawNaturalSum] using ONote.omega0_le_oadd e c t
  | oadd f d u =>
    haveI : ONote.NF e := he
    haveI : ONote.NF f := hb.fst
    have hc := ONote.cmp_compares e f
    cases h : ONote.cmp e f with
    | lt =>
      have hef : e.repr < f.repr := by simpa only [h, Ordering.Compares, ONote.lt_def] using hc
      exact (Ordinal.opow_le_opow_right Ordinal.omega0_pos hef.le).trans
        (by simpa only [rawNaturalSum, h] using
          (ONote.omega0_le_oadd f d (rawNaturalSum (.oadd e c t) u)))
    | eq => simpa only [rawNaturalSum, h] using ONote.omega0_le_oadd e (c + d) (rawNaturalSum t u)
    | gt => simpa only [rawNaturalSum, h] using ONote.omega0_le_oadd e c (rawNaturalSum t (.oadd f d u))

private theorem sum_zero (a : ONote) : rawNaturalSum a .zero = a := by cases a <;> simp only [rawNaturalSum]

theorem actualOmegaNaturalProductInfinite : Targets.ActualOmegaNaturalProductInfinite := by
  intro a ha hae
  obtain ⟨y, hy⟩ := normalRepresentationComplete a hae
  let x : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  have hx : x.1.repr = Ordinal.omega0 := by simp [x, ONote.repr]
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  simp only [naturalProduct]
  rw [hx]
  rcases y with ⟨y, hny⟩
  cases y with
  | zero => simp only [ONote.repr] at hy; rw [← hy] at ha; exact False.elim (lt_irrefl _ ha)
  | oadd e c t =>
    have hpos : (1 : Ordinal) ≤ (rawNaturalSum 1 e).repr := by
      have hz := head_le_sum .zero 1 .zero e ONote.NF.zero hny.fst
      change Ordinal.omega0 ^ 0 ≤ (rawNaturalSum 1 e).repr at hz
      simpa only [Ordinal.opow_zero] using hz
    have hexp : Ordinal.omega0 ≤ Ordinal.omega0 ^ (rawNaturalSum 1 e).repr := by
      simpa only [Ordinal.opow_one] using Ordinal.opow_le_opow_right Ordinal.omega0_pos hpos
    simp only [x, rawNaturalProduct, sum_zero, rawMonomialProduct]
    exact hexp.trans (head_le_sum (rawNaturalSum 1 e) (1 * c) .zero
      (rawMonomialProduct 1 1 t)
      (rawNaturalSum_normal 1 e (by infer_instance) hny.fst)
      (rawMonomialProduct_normal 1 (by infer_instance) 1 t hny.snd))

end LogicLineages.OrdinalComparison.Source.OriginalDomain
