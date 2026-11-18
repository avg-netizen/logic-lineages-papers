module
public import LogicLineages.PermittedControl.EqualGapCertificateProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem equalGapSourceTail : Targets.EqualGapSourceTail := by
  intro mu nu delta hmud hnud hdl f B hf t ht
  have hmu := normalRepresentationSound mu
  have hnu := normalRepresentationSound nu
  have hd := normalRepresentationSound delta
  have hsum := epsilonZero_add_principal hmu hd
  have hsum' := epsilonZero_add_principal hnu hd
  have hlim := Ordinal.isSuccLimit_add mu.1.repr hdl
  have hlim' := Ordinal.isSuccLimit_add nu.1.repr hdl
  have hitail := equalGap_tail_initial mu nu delta B t ht
  have hR := initial_radius_bounds mu.1.repr nu.1.repr delta.1.repr
  have hlarge := sensitive_tail_large _ B t hitail
  have hnorm := relativeNorm mu.1.repr delta.1.repr hmu hd
  have hnorm' := relativeNorm nu.1.repr delta.1.repr hnu hd
  have hbudget : actualOrdinalNorm (mu.1.repr+delta.1.repr) ≤ t := by
    dsimp only [initialPeelingRadius] at hlarge
    omega
  have hbudget' : actualOrdinalNorm (nu.1.repr+delta.1.repr) ≤ t := by
    dsimp only [initialPeelingRadius] at hlarge
    omega
  have hA := count_initial_facts (mu.1.repr+delta.1.repr) t hsum hlim hbudget
  have hA' := count_initial_facts (nu.1.repr+delta.1.repr) t hsum' hlim' hbudget'
  have hp : actualLimitPart (countInitial (mu.1.repr+delta.1.repr) t)=mu.1.repr+delta.1.repr :=
    limitPart_tail _ hlim _
  have hp' : actualLimitPart (countInitial (nu.1.repr+delta.1.repr) t)=nu.1.repr+delta.1.repr :=
    limitPart_tail _ hlim' _
  obtain ⟨tau,sigma,hHit,hHit',_,_,hcompare⟩ := actualEqualGapCertificate f B hf mu nu delta _ _ t
    hmud hnud hdl hA.1 hA'.1 ht hp hp' hA.2.1 hA'.2.1
  refine ⟨tau,sigma,hHit,hHit',?_,?_,?_⟩
  · intro h
    exact (numericalComparison_zero _ _).mp (hcompare.trans h)
  · intro h
    exact (numericalComparison_one _ _).mp (hcompare.trans h)
  · intro h
    exact (numericalComparison_two _ _).mp (hcompare.trans h)

 theorem fullEqualGapCertificate : Targets.FullEqualGapCertificate :=
  ⟨equalGapCertificateEffective,actualEqualGapCertificate,equalGapSourceTail⟩
end LogicLineages.PermittedControl
