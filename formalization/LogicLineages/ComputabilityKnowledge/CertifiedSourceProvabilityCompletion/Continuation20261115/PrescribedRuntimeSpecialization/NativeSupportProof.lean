module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeSupportProof
open GorbowSyntax GorbowTheoryProof GorbowFormulaSubstitution
open EffectiveNumeral.Family
/-- The exact singleton witness displayed by original HasCertificates.logical. -/
theorem singletonEffective {alpha : Type} [Primcodable alpha] {n : Nat}
 (w : alpha → GorbowPACore.LogicalInstance n)
 (hw : Primrec (fun x => GorbowLogicalAxiomCode.encode (w x))) :
 Primrec (fun x => GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (w x)]) := by
 have hcompile := GorbowLogicalAxiomCodeProof.uniformPrograms.2.2.comp
  ((Primrec.const n).pair hw)
 have hraw : Primrec (fun x => GorbowFormulaPrefixCode.encode (GorbowPACore.logicalFormula (w x))) := by
  have hg := Primrec.option_getD.comp hcompile (Primrec.const [])
  apply hg.of_eq
  intro x
  have he := (GorbowLogicalAxiomCodeProof.exactCompilation n _ _).mpr ⟨w x,rfl,rfl⟩
  rw [he]
  rfl
 have hline : Primrec (fun x => GorbowProofChecker.logicalLine (w x)) :=
  (Primrec.const n).pair (hraw.pair ((Primrec.const 0).pair
   ((Primrec.fst.comp hw).pair ((Primrec.snd.comp hw).pair
    ((Primrec.const 0).pair (Primrec.const 0))))))
 exact Primrec.encode.comp (Primrec.list_cons.comp hline (Primrec.const []))
theorem instantiateLift {n : Nat} (f : Formula (n+1)) (sigma : Fin (n+1) → Term 0) :
 GorbowStandardInstances.instantiate
  (substituteFormula (liftSubstitute (fun i => sigma i.succ)) f) (sigma 0) =
 substituteFormula sigma f := by
 unfold GorbowStandardInstances.instantiate
 rw [GorbowFormulaCompositionProof.composition]
 congr 1
 funext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i =>
  simp only [liftSubstitute,Fin.cases_succ,renameTerm]
  rw [GorbowSubstitution.substitute_composition]
  have he : (fun j : Fin 0 => GorbowSubstitution.substitute
   (Fin.cases (sigma 0) Term.var) (Term.var j.succ)) = Term.var := by
   funext j
   exact Fin.elim0 j
  rw [he]
  exact GorbowSubstitution.substitute_variables (sigma i.succ)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeSupportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.NativeSupportProof
