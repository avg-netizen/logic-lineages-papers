module
public import LogicLineages.OrdinalComparison.NaturalSumTargets
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Constructive natural sum by merging the two hereditary Cantor lists.
Equal exponents retain the sum of their coefficients. Lesser monomials are
retained rather than absorbed, as they would be by ordinary ordinal addition.

Paper 05, `lem:finite-balls`: natural-sum algorithm and norm-additivity portion.
The finite normal-form enumeration and natural product remain separate.
-/

namespace LogicLineages.OrdinalComparison

open Vendor.R1

def rawNaturalSum : ONote → ONote → ONote
  | .zero, b => b
  | a, .zero => a
  | a@(.oadd e c t), b@(.oadd f d u) =>
      match ONote.cmp e f with
      | .lt => .oadd f d (rawNaturalSum a u)
      | .eq => .oadd e (c + d) (rawNaturalSum t u)
      | .gt => .oadd e c (rawNaturalSum t b)
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem rawNaturalSum_coefficients : ∀ (a b q : ONote),
    cantorCoefficient (rawNaturalSum a b) q =
      cantorCoefficient a q + cantorCoefficient b q
  | .zero, b, q => by simp [rawNaturalSum, cantorCoefficient]
  | a, .zero, q => by simp [rawNaturalSum, cantorCoefficient]
  | a@(.oadd e c t), b@(.oadd f d u), q => by
      cases h : ONote.cmp e f with
      | lt =>
          simp only [rawNaturalSum, h, cantorCoefficient,
            rawNaturalSum_coefficients a u q]
          omega
      | eq =>
          have hef : e = f := ONote.eq_of_cmp_eq h
          subst f
          simp only [rawNaturalSum, h, cantorCoefficient,
            rawNaturalSum_coefficients t u q, PNat.add_coe]
          split <;> omega
      | gt =>
          simp only [rawNaturalSum, h, cantorCoefficient,
            rawNaturalSum_coefficients t b q]
          omega
termination_by a b _ => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem rawNaturalSum_norm : ∀ a b : ONote,
    treeWeight (rawNaturalSum a b) = treeWeight a + treeWeight b
  | .zero, b => by simp [rawNaturalSum, treeWeight]
  | a, .zero => by simp [rawNaturalSum, treeWeight]
  | a@(.oadd e c t), b@(.oadd f d u) => by
      cases h : ONote.cmp e f with
      | lt =>
          simp only [rawNaturalSum, h, treeWeight, rawNaturalSum_norm a u]
          omega
      | eq =>
          have hef : e = f := ONote.eq_of_cmp_eq h
          subst f
          simp only [rawNaturalSum, h, treeWeight, rawNaturalSum_norm t u,
            PNat.add_coe, Nat.add_mul]
          omega
      | gt =>
          simp only [rawNaturalSum, h, treeWeight, rawNaturalSum_norm t b]
          omega
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem rawNaturalSum_below : ∀ (a b : ONote) (bound : Ordinal),
    ONote.NFBelow a bound → ONote.NFBelow b bound →
      ONote.NFBelow (rawNaturalSum a b) bound
  | .zero, b, _, _, hb => by simpa only [rawNaturalSum] using hb
  | a, .zero, _, ha, _ => by simpa only [rawNaturalSum] using ha
  | a@(.oadd e c t), b@(.oadd f d u), bound, ha, hb => by
      haveI : ONote.NF e := ha.fst
      haveI : ONote.NF f := hb.fst
      have hc := ONote.cmp_compares e f
      cases h : ONote.cmp e f with
      | lt =>
          have hef : e.repr < f.repr := by simpa only [h, Ordering.Compares] using hc
          have halow : ONote.NFBelow a f.repr :=
            ONote.NF.below_of_lt hef ⟨⟨bound, ha⟩⟩
          simpa only [rawNaturalSum, h] using
            ONote.NFBelow.oadd (n := d) hb.fst
              (rawNaturalSum_below a u f.repr halow hb.snd) hb.lt
      | eq =>
          have hef : e = f := ONote.eq_of_cmp_eq h
          subst f
          simpa only [rawNaturalSum, h] using
            ONote.NFBelow.oadd (n := c + d) ha.fst
              (rawNaturalSum_below t u e.repr ha.snd hb.snd) ha.lt
      | gt =>
          have hfe : f.repr < e.repr := by simpa only [h, Ordering.Compares] using hc
          have hblow : ONote.NFBelow b e.repr :=
            ONote.NF.below_of_lt hfe ⟨⟨bound, hb⟩⟩
          simpa only [rawNaturalSum, h] using
            ONote.NFBelow.oadd (n := c) ha.fst
              (rawNaturalSum_below t b e.repr ha.snd hblow) ha.lt
termination_by a b _ => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem rawNaturalSum_normal (a b : ONote) (ha : ONote.NF a) (hb : ONote.NF b) :
    ONote.NF (rawNaturalSum a b) := by
  obtain ⟨ba, hba⟩ := ha.out
  obtain ⟨bb, hbb⟩ := hb.out
  exact ⟨⟨max ba bb, rawNaturalSum_below a b (max ba bb)
    (hba.mono (le_max_left _ _)) (hbb.mono (le_max_right _ _))⟩⟩

def naturalSum (a b : NONote) : NONote :=
  ⟨rawNaturalSum a.1 b.1, rawNaturalSum_normal a.1 b.1 a.2 b.2⟩

theorem naturalSumCoefficients : Targets.NaturalSumCoefficients naturalSum :=
  fun a b q => rawNaturalSum_coefficients a.1 b.1 q

theorem naturalSumNormAdditive : Targets.NaturalSumNormAdditive naturalSum :=
  fun a b => rawNaturalSum_norm a.1 b.1

end LogicLineages.OrdinalComparison
