module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralImplicationProof

@[expose] public section
/-! Effective original numeric existential introduction for the HB3 code
constructor. The original Hilbert axioms suffice; no theorem-rule extension,
assumed local proof transformer or added source axiom is used. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
open GorbowSyntax
variable {alpha : Type} [Primcodable alpha]

namespace FormulaEffective

theorem neg {n : Nat} {a : alpha → Formula n} (ha : FormulaEffective a) :
    FormulaEffective (fun x => Formula.neg (a x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const 6).pair ha)

theorem ex {n : Nat} {a : alpha → Formula (n+1)} (ha : FormulaEffective a) :
    FormulaEffective (fun x => Formula.ex (a x)) :=
  GorbowCodeConstructorsProof.uniformPrograms.2.1.comp ((Primrec.const 11).pair ha)

end FormulaEffective

namespace HasCertificates

theorem classicalContraposition (ax : alpha → List Nat → Bool) {n : Nat}
    {a b : alpha → Formula n} (ha : FormulaEffective a) (hb : FormulaEffective b) :
    HasCertificates ax (fun x => Formula.imp (.imp (.neg (a x)) (.neg (b x)))
      (.imp (b x) (a x))) :=
  logical ax (fun x => .classicalContraposition (a x) (b x)) ((Primrec.const 2).pair
    (Primrec.list_cons.comp ha (Primrec.list_cons.comp hb (Primrec.const []))))

/-- A fixed finite proof schema, effective in the literal formula code. -/
theorem doubleNegation (ax : alpha → List Nat → Bool) {n : Nat}
    {p : alpha → Formula n} (hp : FormulaEffective p) :
    HasCertificates ax (fun x => Formula.imp (.neg (.neg (p x))) (p x)) := by
  let R := fun _ : alpha => (Formula.equal .zero .zero : Formula n)
  have hR : FormulaEffective R := FormulaEffective.constant _
  have hA := hp.neg.neg
  have hC1 := classicalContraposition ax hR.neg hp.neg
  have hK := k ax hA hR.neg.neg
  have hfirst := compose ax hA (hR.neg.neg.imp hA) (hp.neg.imp hR.neg) hC1 hK
  have hC2 := classicalContraposition ax hp hR
  have hsecond := compose ax hA (hp.neg.imp hR.neg) (hR.imp hp) hC2 hfirst
  have htruth : HasCertificates ax R := reflexive ax (TermEffective.constant (Term.zero : Term n))
  exact mpUnder ax hA hR hp hsecond (lift ax hR hA htruth)

theorem existentialIntroductionRule (ax : alpha → List Nat → Bool) {n : Nat}
    {a : alpha → Formula (n+1)} {t : alpha → Term n}
    (ha : FormulaEffective a) (ht : TermEffective t) :
    HasCertificates ax (fun x => Formula.imp
      (GorbowStandardInstances.instantiate (a x) (t x)) (.ex (a x))) := by
  let P := fun x => Formula.all (.neg (a x))
  let I := fun x => GorbowStandardInstances.instantiate (a x) (t x)
  have hP : FormulaEffective P := ha.neg.all
  have hI : FormulaEffective I := ha.instantiated ht
  have hInstantiate : HasCertificates ax (fun x => Formula.imp (P x) (.neg (I x))) :=
    allInstantiation ax ha.neg ht
  have hDNE := doubleNegation ax hP
  have hbridge := compose ax hP.neg.neg hP hI.neg hInstantiate hDNE
  have hC := classicalContraposition ax hP.neg hI
  have hneg := mp ax (hI.imp hP.neg) hC hbridge
  have hex : HasCertificates ax (fun x => Formula.imp (.neg (P x)) (.ex (a x))) :=
    logical ax (fun x => .existsDualBackward (a x)) ((Primrec.const 10).pair
      (Primrec.list_cons.comp ha (Primrec.const [])))
  exact compose ax hI hP.neg ha.ex hex hneg

theorem existentialIntroduction (ax : alpha → List Nat → Bool) {n : Nat}
    {a : alpha → Formula (n+1)} {t : alpha → Term n}
    (ha : FormulaEffective a) (ht : TermEffective t)
    (h : HasCertificates ax (fun x => GorbowStandardInstances.instantiate (a x) (t x))) :
    HasCertificates ax (fun x => Formula.ex (a x)) :=
  mp ax ha.ex (existentialIntroductionRule ax ha ht) h

end HasCertificates
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family
