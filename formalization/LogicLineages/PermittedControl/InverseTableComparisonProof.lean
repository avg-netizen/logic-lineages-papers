module
public import LogicLineages.PermittedControl.InverseTableTargets
public import LogicLineages.PermittedControl.GapInputProof
public import LogicLineages.PermittedControl.EqualGapCertificateSourceProof
public import LogicLineages.PermittedControl.CocycleProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem inverse_input_comparison (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (a mu b nu : Ordinal.{0}) (ha : a<epsilonZero) (hb : b<epsilonZero)
    (hal : Order.IsSuccLimit a) (hbl : Order.IsSuccLimit b)
    (hm : mu=0 ∨ Order.IsSuccLimit mu) (hn : nu=0 ∨ Order.IsSuccLimit nu)
    (hma : mu<a) (hnb : nu<b) (he : b-nu≤a-mu)
    (t u i j : Nat) (ht : gapInputTail a mu b nu 0≤t)
    (hu : gapInputTail a mu b nu 0≤u) (hut : u<t)
    (hi : FirstEntry f (countInitial a t) mu i)
    (hj : FirstEntry f (countInitial b u) nu j) :
    entryNormAt f (countInitial b u) j < entryNormAt f (countInitial a t) i := by
  obtain ⟨i',j',hi',hj',_,h⟩ :=
    (gapInputComparison f B hf a mu b nu ha hb hal hbl hm hn hma hnb).2.1 he t u ht hu hut
  have ei := firstEntry_unique f _ _ i i' hi hi'
  have ej := firstEntry_unique f _ _ j j' hj hj'
  simpa only [ei,ej] using h

 theorem inverse_table_rows (sign y h q p : Nat) (hh : 0<h)
    (hlt : y<h → q<p) (hgt : h<y → p<q)
    (heq : y=h → numericalComparison p q=sign) : InverseTableRows sign y h q p := by
  have hz := numericalComparison_zero p q
  have ho := numericalComparison_one p q
  have ht := numericalComparison_two p q
  unfold InverseTableRows
  constructor
  · intro hs
    by_cases hy : y<h
    · have hx := hlt hy
      omega
    · by_cases hy' : h<y
      · have hx := hgt hy'
        omega
      · have he : y=h := by omega
        have hx := ho.mp ((heq he).trans hs)
        omega
  constructor
  · intro hs
    by_cases hy : y<h
    · have hx := hlt hy
      omega
    · by_cases hy' : h<y
      · have hx := hgt hy'
        omega
      · have he : y=h := by omega
        have hx := ht.mp ((heq he).trans hs)
        omega
  · intro hs
    by_cases hy : y<h
    · have hx := hlt hy
      omega
    · by_cases hy' : h<y
      · have hx := hgt hy'
        omega
      · have he : y=h := by omega
        have hx := hz.mp ((heq he).trans hs)
        omega

end LogicLineages.PermittedControl
