module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralImplicationProof

@[expose] public section
/-! Primitive recursion assembles the original numeric certificates from an
accepted base and accepted ordinary STEP IMPLICATIONS. The induction proof
supplies the actual prior acceptance; there is no arbitrary-certificate oracle. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family.HasCertificates
open GorbowSyntax GorbowSortedSyntaxCode GorbowTheoryCertificateOperations

/-- Source checker parameters remain fixed while the recursion counter grows. -/
theorem recursionFamily {beta : Type} [Primcodable beta]
    (ax : beta → List Nat → Bool) (phi : Nat × beta → Sentence)
    (hphi : FormulaEffective phi)
    (hbase : HasCertificates ax (fun p => phi (0,p)))
    (hstep : HasCertificates (fun z : Nat × beta => ax z.2)
      (fun z => Formula.imp (phi (z.1,z.2)) (phi (z.1+1,z.2)))) :
    HasCertificates (fun z : Nat × beta => ax z.2) phi := by
  obtain ⟨base, hbasePR, hbaseOK⟩ := hbase
  obtain ⟨step, hstepPR, hstepOK⟩ := hstep
  let produce : Nat × beta → Nat := fun z =>
    Nat.rec (motive := fun _ => Nat) (base z.2)
      (fun k previous => mpCertificate 0 (formulaCode (phi (k+1,z.2))) (step (k,z.2)) previous) z.1
  have hparam : Primrec (fun w : (Nat × beta) × (Nat × Nat) => w.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hcount : Primrec (fun w : (Nat × beta) × (Nat × Nat) => w.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hprevious : Primrec (fun w : (Nat × beta) × (Nat × Nat) => w.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hnext := hphi.sortedCode.comp ((Primrec.succ.comp hcount).pair hparam)
  have hstepAt := hstepPR.comp (hcount.pair hparam)
  have hjoin : Primrec (fun w : (Nat × beta) × (Nat × Nat) =>
      mpCertificate 0 (formulaCode (phi (w.2.1+1,w.1.2)))
        (step (w.2.1,w.1.2)) w.2.2) :=
    GorbowTheoryCertificateOperationsProof.effectiveModusPonens.comp
      ((Primrec.const 0).pair (hnext.pair (hstepAt.pair hprevious)))
  have hproduce : Primrec produce :=
    Primrec.nat_rec' Primrec.fst (hbasePR.comp Primrec.snd) hjoin.to₂
  have hcorrect : ∀ k p, GorbowTheoryNumericCertificate.check (ax p) 0
      (formulaCode (phi (k,p))) (produce (k,p)) = true := by
    intro k
    induction k with
    | zero =>
        intro p
        exact hbaseOK p
    | succ k ih =>
        intro p
        change GorbowTheoryNumericCertificate.check (ax p) 0 (formulaCode (phi (k+1,p)))
          (mpCertificate 0 (formulaCode (phi (k+1,p))) (step (k,p)) (produce (k,p))) = true
        exact GorbowTheoryCertificateOperationsProof.numericModusPonens (ax p) 0
          (phi (k,p)) (phi (k+1,p)) (step (k,p)) (produce (k,p)) (hstepOK (k,p)) (ih p)
  exact ⟨produce, hproduce, fun z => hcorrect z.1 z.2⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeral.Family.HasCertificates
