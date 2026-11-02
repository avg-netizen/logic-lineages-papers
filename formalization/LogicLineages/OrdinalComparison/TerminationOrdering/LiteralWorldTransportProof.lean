module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess LambdaObservationMatching LiteralWorldTransport

theorem consPortTransport : LiteralWorldTransportTargets.ConsPortTransport := by
  intro Symbol inst arity I P σ i hQ τ v
  have hd := ((FiniteObservationBitsProof.worldCalibration Symbol arity I ((i,σ)::P.val)).mp hQ).1
  apply LiteralVariableValueProof.nameInjective (budget I) I.context ((i,σ)::P.val) hd τ
  exact LiteralVariableValueProof.nameExtension (budget I) I.context P.val ((i,σ)::P.val)
    (fun p hp => List.mem_cons_of_mem _ hp) τ v

theorem openingIdentity : LiteralWorldTransportTargets.OpeningIdentity := by
  intro Symbol inst arity I P σ υ i h
  let Q : World I := ⟨(i,σ)::P.val,h.2.1⟩
  have he := TypedValueEnvironmentProof.identityTransport Symbol inst arity I P Q (fun p hp => List.mem_cons_of_mem _ hp)
  funext τ v
  cases v with
  | here => rfl
  | there v =>
    exact (congrArg (fun env : Environment I (portTypes P.val++I.context) Q => env v) he).trans
      (congrArg (fun w : Variable (portTypes Q.val++I.context) τ => identity I Q w)
        (consPortTransport Symbol inst arity I P σ i h.2.1 τ v))

theorem sourceIdentityWeakening : LiteralWorldTransportTargets.SourceIdentityWeakening := by
  intro Symbol inst arity I M P Q h τ q
  have hr := StructuralRenamingProof.interpretationCovariance Symbol inst arity I _ _ τ
    (LiteralVariableValue.extendVariables I.context Q.val P.val h) q M Q (identity I Q)
  have he := TypedValueEnvironmentProof.identityTransport Symbol inst arity I P Q h
  exact hr.trans ((congrArg (fun env : Environment I (portTypes P.val++I.context) Q => interpret q M Q env) he.symm).trans
    ((action q).evaluateNatural M P Q h (identity I P)).symm)

theorem sourceReadTransport : LiteralWorldTransportTargets.SourceReadTransport := by
  intro Symbol inst arity I M P Q h τ q strict o ho
  exact (congrArg (fun a : Value I τ Q => readBit strict a o)
    (sourceIdentityWeakening Symbol inst arity I M P Q h τ q)).trans
    (TypedObservationAccessProof.restrictionAccess Symbol inst arity I τ P strict Q h
      (interpret q M P (identity I P)) o ho)

end LogicLineages.OrdinalComparison.TerminationOrdering.LiteralWorldTransportProof
