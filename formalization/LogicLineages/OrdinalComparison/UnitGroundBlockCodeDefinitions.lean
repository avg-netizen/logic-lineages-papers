module
public import LogicLineages.OrdinalComparison.OneUnitCodeDefinitions
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceUnitEliminationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode

abbrev Payload (α : Type) := Nat × Nat × Nat × Nat × α

def blockCode {α : Type} {Γ : List Ty} (b : UnitElimination.GroundBlock α Γ) : Payload α :=
  (Γ.length,SyntaxCode.encodeTerm b.left,SyntaxCode.encodeTerm b.right,b.factor,b.anchor)

/-- Preserve both literal applications and both unused binders of the source
probe, including the real output-type binder; no beta reduction occurs. -/
def probeCode (τ src x : Nat) : Nat :=
  8*Nat.pair (OneUnitCode.firstCode τ 1)
    (8*Nat.pair (OneUnitCode.unusedCode src) (8*x)+5)+5

def originalProbeCode (τ src : Nat) : Nat :=
  probeCode τ (ContextInsertionCode.sourceCode 0 2 src) 0

def closedProbeCode (n τ src : Nat) : Nat :=
  probeCode τ (ContextInsertionCode.sourceCode 0 (n+2) (GroundClosingCode.closeCode 0 src)) 1

def buildCode (n τ src : Nat) : Payload (Nat×Nat) :=
  (n,originalProbeCode τ src,closedProbeCode n τ src,OneUnitCode.coefficientCode τ,(n,src))

noncomputable def anchorValue (b : Payload (Nat×Nat)) : Nat :=
  AbsoluteObserver.openSourceValue b.2.2.2.2

noncomputable def realizeCode (b : Payload (Nat×Nat)) : Payload Nat :=
  (b.1,b.2.1,b.2.2.1,b.2.2.2.1,anchorValue b)

noncomputable def realizedBlock {Γ : List Ty} (b : UnitElimination.GroundBlock (Nat×Nat) Γ) :
    UnitElimination.GroundBlock Nat Γ :=
  ⟨b.allGround,b.left,b.right,b.factor,AbsoluteObserver.openSourceValue b.anchor⟩
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode
