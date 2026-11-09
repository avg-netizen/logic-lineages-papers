module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralEqualityProof

@[expose] public section
/-! Effective ordinary implications for the recursion case. The prior numeric
certificate is consumed only by original MP; no arbitrary certificate is
assumed accepted when synthesizing the step implication's certificate. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family.HasCertificates
open GorbowSyntax GorbowClosedEquality GorbowClosedEqualityProof
variable {alpha : Type} [Primcodable alpha]

theorem k (ax : alpha → List Nat → Bool) {n : Nat} {a b : alpha → Formula n}
    (ha : FormulaEffective a) (hb : FormulaEffective b) :
    HasCertificates ax (fun x => Formula.imp (a x) (.imp (b x) (a x))) :=
  logical ax (fun x => .k (a x) (b x)) ((Primrec.const 0).pair
    (Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (Primrec.const []))))

theorem s (ax : alpha → List Nat → Bool) {n : Nat} {a b c : alpha → Formula n}
    (ha : FormulaEffective a) (hb : FormulaEffective b) (hc : FormulaEffective c) :
    HasCertificates ax (fun x => Formula.imp (.imp (a x) (.imp (b x) (c x)))
      (.imp (.imp (a x) (b x)) (.imp (a x) (c x)))) :=
  logical ax (fun x => .s (a x) (b x) (c x)) ((Primrec.const 1).pair
    (Primrec.list_cons.comp ha (Primrec.list_cons.comp hb
      (Primrec.list_cons.comp hc (Primrec.const [])))))

theorem lift (ax : alpha → List Nat → Bool) {n : Nat} {a b : alpha → Formula n}
    (ha : FormulaEffective a) (hb : FormulaEffective b) (h : HasCertificates ax a) :
    HasCertificates ax (fun x => Formula.imp (b x) (a x)) :=
  mp ax (hb.imp ha) (k ax ha hb) h

theorem mpUnder (ax : alpha → List Nat → Bool) {n : Nat} {p q r : alpha → Formula n}
    (hp : FormulaEffective p) (hq : FormulaEffective q) (hr : FormulaEffective r)
    (hi : HasCertificates ax (fun x => Formula.imp (p x) (.imp (q x) (r x))))
    (ha : HasCertificates ax (fun x => Formula.imp (p x) (q x))) :
    HasCertificates ax (fun x => Formula.imp (p x) (r x)) :=
  mp ax (hp.imp hr) (mp ax ((hp.imp hq).imp (hp.imp hr)) (s ax hp hq hr) hi) ha

theorem compose (ax : alpha → List Nat → Bool) {n : Nat} {p q r : alpha → Formula n}
    (hp : FormulaEffective p) (hq : FormulaEffective q) (hr : FormulaEffective r)
    (hqr : HasCertificates ax (fun x => Formula.imp (q x) (r x)))
    (hpq : HasCertificates ax (fun x => Formula.imp (p x) (q x))) :
    HasCertificates ax (fun x => Formula.imp (p x) (r x)) :=
  mpUnder ax hp hq hr (lift ax (hq.imp hr) hp hqr) hpq

theorem unaryCongruenceRule (ax : alpha → List Nat → Bool)
    {f : alpha → Term 1} {t u : alpha → Term 0}
    (hf : TermEffective f) (ht : TermEffective t) (hu : TermEffective u) :
    HasCertificates ax (fun x => Formula.imp (.equal (t x) (u x))
      (.equal (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (u x)))) := by
  have hft := hf.instantiated ht
  have hfu := hf.instantiated hu
  let matrix := fun x => Formula.equal (liftClosedTerm 1 (instantiateTerm (f x) (t x))) (f x)
  have hm : FormulaEffective matrix := FormulaEffective.equal hft.liftedClosed hf
  have he := equalityReplacement ax hm ht hu
  have he' : HasCertificates ax (fun x => Formula.imp (.equal (t x) (u x))
      (.imp (.equal (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (t x)))
        (.equal (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (u x))))) := by
    simpa only [matrix, instantiatedEqual, instantiateLift] using he
  have hp := FormulaEffective.equal ht hu
  have hq := FormulaEffective.equal hft hft
  have hr := FormulaEffective.equal hft hfu
  exact mpUnder ax hp hq hr he' (lift ax hq hp (reflexive ax hft))

theorem transitivityUnder (ax : alpha → List Nat → Bool)
    {p : alpha → Formula 0} {t u v : alpha → Term 0}
    (hp : FormulaEffective p) (ht : TermEffective t) (hu : TermEffective u) (hv : TermEffective v)
    (htu : HasCertificates ax (fun x => Formula.imp (p x) (.equal (t x) (u x))))
    (huv : HasCertificates ax (fun x => Formula.imp (p x) (.equal (u x) (v x)))) :
    HasCertificates ax (fun x => Formula.imp (p x) (.equal (t x) (v x))) := by
  let matrix := fun x => Formula.equal (liftClosedTerm 1 (t x)) (.var 0)
  have hm : FormulaEffective matrix :=
    FormulaEffective.equal ht.liftedClosed (TermEffective.constant (.var 0))
  have he := equalityReplacement ax hm hu hv
  have he' : HasCertificates ax (fun x => Formula.imp (.equal (u x) (v x))
      (.imp (.equal (t x) (u x)) (.equal (t x) (v x)))) := by
    simpa only [matrix, instantiatedEqual, instantiateLift, instantiateVariable] using he
  have htuE := FormulaEffective.equal ht hu
  have huvE := FormulaEffective.equal hu hv
  have htvE := FormulaEffective.equal ht hv
  have hr := mpUnder ax hp huvE (htuE.imp htvE)
    (lift ax (huvE.imp (htuE.imp htvE)) hp he') huv
  exact mpUnder ax hp htuE htvE hr htu

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family.HasCertificates
