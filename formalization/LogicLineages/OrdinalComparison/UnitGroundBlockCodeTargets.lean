module
public import LogicLineages.OrdinalComparison.UnitGroundBlockCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Targets

def ExactProbeCodes : Prop :=
  (∀ (Γ : List Ty) (τ : Ty) (t : OriginalTerm Γ τ),
    originalProbeCode (SyntaxCode.typeCode τ) (SyntaxCode.encodeTerm t) =
      SyntaxCode.encodeTerm (AbsoluteObserver.originalProbe t)) ∧
  ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (τ : Ty) (t : OriginalTerm Γ τ),
    closedProbeCode Γ.length (SyntaxCode.typeCode τ) (SyntaxCode.encodeTerm t) =
      SyntaxCode.encodeTerm (AbsoluteObserver.closedProbe hΓ t)

def ExactGroundBlock : Prop := ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground)
    (τ : Ty) (t : OriginalTerm Γ τ),
  buildCode Γ.length (SyntaxCode.typeCode τ) (SyntaxCode.encodeTerm t) =
    blockCode (UnitElimination.groundBlock hΓ t)

def EffectiveAlgorithms : Prop :=
  Primrec (fun p : Nat×Nat×Nat => probeCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ originalProbeCode ∧
  Primrec (fun p : Nat×Nat×Nat => closedProbeCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat×Nat×Nat => buildCode p.1 p.2.1 p.2.2) ∧
  Computable anchorValue ∧ Computable realizeCode

/-- The program is the genuine original (ground-context length, source code),
not a supplied value. Only the established actual source evaluator runs it. -/
def ActualAnchorCalibration : Prop :=
  (∀ (Γ : List Ty) (b : UnitElimination.GroundBlock (Nat×Nat) Γ),
    realizeCode (blockCode b) = blockCode (realizedBlock b)) ∧
  ∀ (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (τ : Ty) (t : OriginalTerm Γ τ),
    anchorValue (buildCode Γ.length (SyntaxCode.typeCode τ) (SyntaxCode.encodeTerm t)) =
      AbsoluteObserver.anchor hΓ t ∧
    0 < anchorValue (buildCode Γ.length (SyntaxCode.typeCode τ) (SyntaxCode.encodeTerm t))
end LogicLineages.OrdinalComparison.Source.UnitGroundBlockCode.Targets
