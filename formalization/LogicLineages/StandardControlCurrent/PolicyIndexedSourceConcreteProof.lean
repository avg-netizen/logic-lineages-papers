module
public import LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompileTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompileProof
public import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentEffectivityProof
public import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBodyTargets
public import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionPartialsTargets
public import LogicLineages.StandardControlCurrent.PolicyIndexedPartialTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedPartialProgramsProof
import LogicLineages.StandardControlCurrent.PolicyIndexedPartialRunProof
import LogicLineages.StandardControlCurrent.PolicyIndexedAbstractionBodyProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedSourceConcrete
open OrdinalComparison Source Source.AdmissibleSum Source.ForwardTranslation
open Nat.Partrec (Code)
open PolicyIndexedAbstractionPartials (PartialArgs PartialBackend ImplementsPartial)
open PolicyIndexedAssignment (Abstraction ImplementsAbstraction AbstractionPartrec)

noncomputable def partialBackend : PartialBackend := fun x =>
  (PolicyIndexedPartial.run (x.1,x.2)).bind Part.ofOption

theorem partialBackendPartrec : Partrec partialBackend :=
  Partrec.bind PolicyIndexedPartial.indexedPartialRunPartrec
    (Computable.ofOption (Computable.snd : Computable
      (Prod.snd : PartialArgs × Option (Option (List Nat)) → Option (Option (List Nat))))).to₂

theorem exactPartialBackend (c : Code) (p : Policy) (h : PolicyIndexedShape.Implements c p) :
    ImplementsPartial partialBackend c p := by
  intro level i n
  unfold partialBackend
  rw [PolicyIndexedPartial.exactIndexedPartialRun c p h,Part.bind_some] <;> rfl

noncomputable def abstraction : Abstraction :=
  fun c i r body => PolicyIndexedAbstractionBody.abstractionCode partialBackend (c,i,r,body)

theorem abstractionPartrec : AbstractionPartrec abstraction :=
  PolicyIndexedAbstractionBody.abstractionPartrec partialBackend partialBackendPartrec

theorem exactAbstraction (c : Code) (p : Policy) (h : PolicyIndexedShape.Implements c p) :
    ImplementsAbstraction abstraction c p :=
  PolicyIndexedAbstractionBody.abstractionExact partialBackend c p h (exactPartialBackend c p h)

noncomputable def compile : PolicyIndexedSourceCompile.Args → Part (Option EncodedVector) :=
  PolicyIndexedSourceCompile.compile abstraction

theorem compilePartrec : Partrec compile :=
  PolicyIndexedSourceCompile.policyIndexedSourceCompileEffectivity abstraction
    (PolicyIndexedAssignment.indexedAssignmentRunPartrec abstraction abstractionPartrec)

theorem compileExact (c : Code) (p : Policy) (h : PolicyIndexedShape.Implements c p)
    (depth code : Nat) : compile (c,depth,code) = Part.some (PolicySourceInterface.compile p depth code) :=
  PolicyIndexedSourceCompile.exactPolicyIndexedSourceCompile abstraction c p h
    (exactAbstraction c p h) depth code

end LogicLineages.StandardControlCurrent.PolicyIndexedSourceConcrete
