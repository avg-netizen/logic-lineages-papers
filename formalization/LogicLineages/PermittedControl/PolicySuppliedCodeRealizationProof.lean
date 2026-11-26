module
public import LogicLineages.PermittedControl.PolicySuppliedCodeRealizationTargets

public section
namespace LogicLineages.PermittedControl.PolicySuppliedCodeRealization
open OrdinalComparison.Source.AdmissibleSum
open StandardControlCurrent
open PolicySuppliedCodeMacro (RealizesPolicy)

theorem effectiveHasCode : EffectiveHasCode := by
  intro p hp
  have hselector : Computable (fun a : Nat × Nat => PolicyShape.selector p a.1 a.2) := hp
  have hraw : Computable (fun z : Nat =>
      Encodable.encode (PolicyShape.selector p z.unpair.1 z.unpair.2)) :=
    Computable.encode.comp (hselector.comp Computable.unpair)
  have hpartial : Partrec (fun z : Nat =>
      Part.some (Encodable.encode (PolicyShape.selector p z.unpair.1 z.unpair.2))) := hraw
  obtain ⟨e, he⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpartial)
  refine ⟨e, ?_⟩
  intro tag n
  simpa only [Nat.unpair_pair] using congrFun he (Nat.pair tag n)

theorem realizedIsEffective : RealizedIsEffective := by
  intro e p he
  have hinput : Computable (fun a : Nat × Nat => Nat.pair a.1 a.2) :=
    Primrec₂.natPair.to_comp
  have heval : Partrec (fun a : Nat × Nat => e.eval (Nat.pair a.1 a.2)) :=
    Nat.Partrec.Code.eval_part.comp (Computable.const e) hinput
  have hencoded : Computable (fun a : Nat × Nat =>
      Encodable.encode (PolicyShape.selector p a.1 a.2)) :=
    heval.of_eq_tot (fun a => Part.eq_some_iff.mp (he a.1 a.2))
  exact Computable.encode_iff.mp hencoded

theorem exactPolicyCodeRealization : ExactPolicyCodeRealization := by
  intro p
  constructor
  · exact effectiveHasCode p
  · rintro ⟨e, he⟩
    exact realizedIsEffective e p he

#print axioms effectiveHasCode
#print axioms realizedIsEffective
#print axioms exactPolicyCodeRealization

end LogicLineages.PermittedControl.PolicySuppliedCodeRealization
