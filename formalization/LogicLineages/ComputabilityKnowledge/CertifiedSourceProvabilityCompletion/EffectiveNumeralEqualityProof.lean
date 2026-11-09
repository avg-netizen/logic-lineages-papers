module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralSpecializationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution GorbowClosedEquality
open GorbowClosedEqualityProof GorbowSubstitution

variable {alpha : Type} [Primcodable alpha]

namespace TermEffective

theorem succ {n : Nat} {t : alpha → Term n} (ht : TermEffective t) :
    TermEffective (fun x => Term.succ (t x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const 2).pair ht)

theorem add {n : Nat} {t u : alpha → Term n} (ht : TermEffective t) (hu : TermEffective u) :
    TermEffective (fun x => Term.add (t x) (u x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
    ((Primrec.const 3).pair (ht.pair hu))

theorem mul {n : Nat} {t u : alpha → Term n} (ht : TermEffective t) (hu : TermEffective u) :
    TermEffective (fun x => Term.mul (t x) (u x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.2.1.comp
    ((Primrec.const 4).pair (ht.pair hu))

theorem universalFunction {n : Nat} {t : alpha → Term n} (ht : TermEffective t) :
    TermEffective (fun x => Term.universalFunction (t x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const 5).pair ht)

end TermEffective

namespace HasCertificates

theorem transitivity (axCheck : alpha → List Nat → Bool) {t u v : alpha → Term 0}
    (ht : TermEffective t) (hu : TermEffective u) (hv : TermEffective v)
    (htu : HasCertificates axCheck (fun x => Formula.equal (t x) (u x)))
    (huv : HasCertificates axCheck (fun x => Formula.equal (u x) (v x))) :
    HasCertificates axCheck (fun x => Formula.equal (t x) (v x)) := by
  let matrix := fun x => Formula.equal (liftClosedTerm 1 (t x)) (.var 0)
  have hm : FormulaEffective matrix :=
    FormulaEffective.equal ht.liftedClosed (TermEffective.constant (.var 0))
  have hr := equalityReplacement axCheck hm hu hv
  have hr' : HasCertificates axCheck (fun x => Formula.imp (.equal (u x) (v x))
      (.imp (.equal (t x) (u x)) (.equal (t x) (v x)))) := by
    simpa only [matrix, instantiatedEqual, instantiateLift, instantiateVariable] using hr
  have htuE := FormulaEffective.equal ht hu
  have htvE := FormulaEffective.equal ht hv
  exact mp axCheck htvE (mp axCheck (htuE.imp htvE) hr' huv) htu

theorem unaryCongruence (axCheck : alpha → List Nat → Bool)
    {f : alpha → Term 1} {t u : alpha → Term 0}
    (hf : TermEffective f) (ht : TermEffective t) (hu : TermEffective u)
    (htu : HasCertificates axCheck (fun x => Formula.equal (t x) (u x))) :
    HasCertificates axCheck (fun x => Formula.equal
      (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (u x))) := by
  have hft := hf.instantiated ht
  have hfu := hf.instantiated hu
  let matrix := fun x => Formula.equal (liftClosedTerm 1 (instantiateTerm (f x) (t x))) (f x)
  have hm : FormulaEffective matrix := FormulaEffective.equal hft.liftedClosed hf
  have hr := equalityReplacement axCheck hm ht hu
  have hr' : HasCertificates axCheck (fun x => Formula.imp (.equal (t x) (u x))
      (.imp (.equal (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (t x)))
        (.equal (instantiateTerm (f x) (t x)) (instantiateTerm (f x) (u x))))) := by
    simpa only [matrix, instantiatedEqual, instantiateLift] using hr
  have hrr := FormulaEffective.equal hft hft
  have hout := FormulaEffective.equal hft hfu
  exact mp axCheck hout (mp axCheck (hrr.imp hout) hr' htu) (reflexive axCheck hft)

private theorem subLift (t x : Term 0) :
    substitute (Fin.cases x Fin.elim0) (liftClosedTerm 1 t) = t :=
  closedTransport 1 t _

theorem addCongruence (axCheck : alpha → List Nat → Bool)
    {a b c d : alpha → Term 0}
    (ha : TermEffective a) (hb : TermEffective b) (hc : TermEffective c) (hd : TermEffective d)
    (hac : HasCertificates axCheck (fun x => Formula.equal (a x) (c x)))
    (hbd : HasCertificates axCheck (fun x => Formula.equal (b x) (d x))) :
    HasCertificates axCheck (fun x => Formula.equal (.add (a x) (b x)) (.add (c x) (d x))) := by
  have hf : TermEffective (fun x => Term.add (.var 0) (liftClosedTerm 1 (b x))) :=
    (TermEffective.constant (.var 0)).add hb.liftedClosed
  have hg : TermEffective (fun x => Term.add (liftClosedTerm 1 (c x)) (.var 0)) :=
    hc.liftedClosed.add (TermEffective.constant (.var 0))
  have hp := unaryCongruence axCheck hf ha hc hac
  have hq := unaryCongruence axCheck hg hb hd hbd
  simp only [instantiateTerm, substitute, Fin.cases_zero, subLift] at hp hq
  exact transitivity axCheck (ha.add hb) (hc.add hb) (hc.add hd) hp hq

theorem mulCongruence (axCheck : alpha → List Nat → Bool)
    {a b c d : alpha → Term 0}
    (ha : TermEffective a) (hb : TermEffective b) (hc : TermEffective c) (hd : TermEffective d)
    (hac : HasCertificates axCheck (fun x => Formula.equal (a x) (c x)))
    (hbd : HasCertificates axCheck (fun x => Formula.equal (b x) (d x))) :
    HasCertificates axCheck (fun x => Formula.equal (.mul (a x) (b x)) (.mul (c x) (d x))) := by
  have hf : TermEffective (fun x => Term.mul (.var 0) (liftClosedTerm 1 (b x))) :=
    (TermEffective.constant (.var 0)).mul hb.liftedClosed
  have hg : TermEffective (fun x => Term.mul (liftClosedTerm 1 (c x)) (.var 0)) :=
    hc.liftedClosed.mul (TermEffective.constant (.var 0))
  have hp := unaryCongruence axCheck hf ha hc hac
  have hq := unaryCongruence axCheck hg hb hd hbd
  simp only [instantiateTerm, substitute, Fin.cases_zero, subLift] at hp hq
  exact transitivity axCheck (ha.mul hb) (hc.mul hb) (hc.mul hd) hp hq

theorem successorCongruence (axCheck : alpha → List Nat → Bool)
    {t u : alpha → Term 0} (ht : TermEffective t) (hu : TermEffective u)
    (h : HasCertificates axCheck (fun x => Formula.equal (t x) (u x))) :
    HasCertificates axCheck (fun x => Formula.equal (.succ (t x)) (.succ (u x))) := by
  have hp := unaryCongruence axCheck (TermEffective.constant (.succ (.var 0))) ht hu h
  simpa only [instantiateTerm, substitute, Fin.cases_zero] using hp

theorem universalFunctionCongruence (axCheck : alpha → List Nat → Bool)
    {t u : alpha → Term 0} (ht : TermEffective t) (hu : TermEffective u)
    (h : HasCertificates axCheck (fun x => Formula.equal (t x) (u x))) :
    HasCertificates axCheck (fun x => Formula.equal (.universalFunction (t x))
      (.universalFunction (u x))) := by
  have hp := unaryCongruence axCheck (TermEffective.constant (.universalFunction (.var 0))) ht hu h
  simpa only [instantiateTerm, substitute, Fin.cases_zero] using hp

end HasCertificates
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
