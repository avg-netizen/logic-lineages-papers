module
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Targets
open SourcePlanSpineCode SourcePrimitiveForestCode ExistentialPlan PrimitiveLowering

def ExactBitTransport : Prop := ∀ {Γ} (bits : List Nat) (base : Nat) (out : Port Γ) (q : Plan Γ),
  ParametricExistentialPlan.Supported q →
  buildBits bits base (portNumber out) (spine q)=
    spine (BinaryPlan.binaryPlan (dagOfBits bits base) out q)

def ExactLiteralTransport : Prop := ∀ {Γ} (k : Nat) (out : Port Γ) (q : Plan Γ),
  ParametricExistentialPlan.Supported q →
  build k (portNumber out) (spine q)=
    spine (BinaryPlan.binaryPlan (SourceAdditionCompletion.binaryDAG k) out q)

def UniformPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat×BinaryState => advance p.1 p.2) ∧
  Primrec (fun p : List Nat×Nat×Nat×List Instruction => buildBits p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat×Nat×List Instruction => build p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Targets
