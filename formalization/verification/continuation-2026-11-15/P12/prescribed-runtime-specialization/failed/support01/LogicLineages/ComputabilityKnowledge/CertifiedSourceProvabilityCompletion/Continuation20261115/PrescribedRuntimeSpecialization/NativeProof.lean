module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeProof
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution GorbowPACore
open EffectiveNumeral.Family
theorem exactWitness : Targets.EffectivePrescribedWitness := by
 intro alpha _ axCheck n
 induction n with
 | zero =>
  intro f sigma antecedent hf hs hc hv
  constructor
  · exact hc
  · intro x
    have he : substituteFormula (sigma x) (f x) = f x := by
     have hz : sigma x = Fin.elim0 := by funext i; exact Fin.elim0 i
     rw [hz]
     exact GorbowClosedDeductionProof.closedSyntax.1 (f x)
    simpa only [produce,he,GorbowStandardInduction.universalClosure] using hv x
 | succ n ih =>
  intro f sigma antecedent hf hs hc hv
  obtain ⟨ht,htcheck⟩ := ih (fun x => .all (f x)) (fun x i => sigma x i.succ)
   antecedent hf.all (fun i => hs i.succ) hc hv
  let B := fun x => substituteFormula (liftSubstitute (fun i => sigma x i.succ)) (f x)
  have hB : FormulaEffective B := by
   apply hf.substitution
   intro i
   cases i using Fin.cases with
   | zero => exact TermEffective.constant (.var 0)
   | succ j =>
    change TermEffective (fun x => renameTerm Fin.succ (sigma x j.succ))
    exact (hs j.succ).substitution (fun i => Fin.elim0 i)
  have hsub : FormulaEffective (fun x => substituteFormula (sigma x) (f x)) :=
   hf.substitution hs
  have hsingle := NativeSupportProof.singletonEffective
   (fun x => LogicalInstance.allInstantiate (B x) (sigma x 0))
   ((Primrec.const 13).pair (Primrec.list_cons.comp hB
    (Primrec.list_cons.comp (hs 0) (Primrec.const []))))
  constructor
  · exact GorbowTheoryCertificateOperationsProof.effectiveModusPonens.comp
     ((Primrec.const 0).pair (hsub.sortedCode.pair (hsingle.pair ht)))
  · intro x
    have hi : GorbowTheoryNumericCertificate.check (axCheck x) 0
     (GorbowSortedSyntaxCode.formulaCode (Formula.imp (.all (B x))
      (GorbowStandardInstances.instantiate (B x) (sigma x 0))))
     (GorbowNumericCertificate.certificateNumber
      [GorbowProofChecker.logicalLine (.allInstantiate (B x) (sigma x 0))]) = true :=
     compiledCertificate (axCheck x) (.logical (.allInstantiate (B x) (sigma x 0)))
    have ha : GorbowTheoryNumericCertificate.check (axCheck x) 0
     (GorbowSortedSyntaxCode.formulaCode (.all (B x)))
     (produce (.all (f x)) (fun i => sigma x i.succ) (antecedent x)) = true := htcheck x
    have hout := GorbowTheoryCertificateOperationsProof.numericModusPonens (axCheck x) 0
     (.all (B x)) (GorbowStandardInstances.instantiate (B x) (sigma x 0)) _ _ hi ha
    have he := NativeSupportProof.instantiateLift (f x) (sigma x)
    change GorbowStandardInstances.instantiate (B x) (sigma x 0) = substituteFormula (sigma x) (f x) at he
    rw [he] at hout
    exact hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeProof
