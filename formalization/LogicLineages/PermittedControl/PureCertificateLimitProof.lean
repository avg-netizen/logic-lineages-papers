module
public import LogicLineages.PermittedControl.PureCertificateSuccessorProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem pure_limit_comparison (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu nu E zeta A A' : Ordinal.{0}) (R t tau sigma : Nat)
    (hmu : mu < epsilonZero) (hnu : nu < epsilonZero) (hE : E < epsilonZero) (hz : zeta < epsilonZero)
    (hA : A < epsilonZero) (hA' : A' < epsilonZero)
    (hmud : mu=0 ∨ Order.IsSuccLimit mu) (hnud : nu=0 ∨ Order.IsSuccLimit nu)
    (hEl : Order.IsSuccLimit E) (hz2 : 2 ≤ zeta) (hzE : zeta < E) (hR : 20 ≤ R)
    (hmuR : actualOrdinalNorm mu ≤ R) (hnuR : actualOrdinalNorm nu ≤ R)
    (hER : actualOrdinalNorm E ≤ R) (hzR : actualOrdinalNorm zeta ≤ R)
    (ht : thickBlockTail R B ≤ t) (hp : actualLimitPart A=mu+Ordinal.omega0^E)
    (hp' : actualLimitPart A'=nu+Ordinal.omega0^E) (hn : actualOrdinalNorm A=t) (hn' : actualOrdinalNorm A'=t)
    (hc : ∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile mu e=relativeProfile mu zeta)
    (hc' : ∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile nu e=relativeProfile nu zeta)
    (hdiff : relativeProfile mu zeta ≠ relativeProfile nu zeta)
    (hHit : FirstEntry f A mu tau) (hHit' : FirstEntry f A' nu sigma) :
    compare (entryNormAt f A tau) (entryNormAt f A' sigma)=compare (relativeProfile nu zeta) (relativeProfile mu zeta) := by
  have hlarge := sensitive_tail_large R B t ht
  have hPw : Ordinal.omega0 ≤ Ordinal.omega0^zeta := Ordinal.left_le_opow _
    ((by norm_num : (0 : Ordinal) < 2).trans_le hz2)
  rcases lt_or_gt_of_ne hdiff with hlt | hgt
  · have hdiv := actualPureLimitSeparation f B hf mu nu E zeta A A' R t hmu hnu hE hz hA hA' hmud hnud
      hEl hz2 hzE hR hmuR hnuR hER hzR ht hp hp' hn hn' hc hc' hlt
    have ho := entry_order_from_oriented f B hf mu nu _ A A' t tau sigma hmu hnu hA hA' hmud hnud hPw
      hn hn' (by omega) (by omega) hHit hHit' ⟨1,hdiv.1,hdiv.2.2.1,hdiv.2.1⟩
    exact (compare_gt_iff_gt.mpr ho).trans (compare_gt_iff_gt.mpr hlt).symm
  · have hdiv := actualPureLimitSeparation f B hf nu mu E zeta A' A R t hnu hmu hE hz hA' hA hnud hmud
      hEl hz2 hzE hR hnuR hmuR hER hzR ht hp' hp hn' hn hc' hc hgt
    have ho := entry_order_from_oriented f B hf nu mu _ A' A t sigma tau hnu hmu hA' hA hnud hmud hPw
      hn' hn (by omega) (by omega) hHit' hHit ⟨1,hdiv.1,hdiv.2.2.1,hdiv.2.1⟩
    exact (compare_lt_iff_lt.mpr ho).trans (compare_lt_iff_lt.mpr hgt).symm

end LogicLineages.PermittedControl
