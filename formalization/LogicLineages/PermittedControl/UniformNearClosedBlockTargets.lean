module
public import LogicLineages.PermittedControl.ClosedBlockDecisionTargets
public import LogicLineages.PermittedControl.StageEmitterGuardTargets
public import LogicLineages.PermittedControl.StageCallbackGuardRenderTargets

@[expose] public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open ClosedBlockDecision (Decides)
open OriginalPrintedRawFamilyFrontend (Args)
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawDriver (HighProgram solve)

/-- The fixed rendering record of the closed-block decision (#1418):
the three gated renderings and the gated guard program. -/
def nearRendering : StageCallbackRawLevel.Rendering :=
  StageEmitter.renderingWith StageCallbackGuardRender.guardCode

/-- ONE procedure of the near-control parameter and the encoded query: the
accepted stage query at the control `nearControl b`, threshold `b+1`, with
the fixed assembled high program. -/
noncomputable def nearDecide (x : Nat × Args) : Option Bool :=
  OriginalPrintedRawStageQuery.result (nearControl x.1) (x.1 + 1)
    (StageEmitter.highCode nearRendering) x.2

/-- The accepted per-control effectivity of the raw driver (#1340), redone
with the control and the bound program depending computably on a parameter. -/
def ParametricSolveEffectivity : Prop :=
  ∀ (α : Type) [Primcodable α] (F : α → Nat → Nat) (bound : α → RawFamily → Nat) (high : HighProgram),
    Computable₂ F → Computable₂ bound → Computable high →
      Computable (fun x : α × RawFamily => solve (F x.1) (bound x.1) high x.2)

/-- Joint computability in `b` and the encoded query. -/
def NearDecideComputable : Prop := Computable nearDecide

/-- Correctness at every `b`, literally `Decides` of the closed-block comparator. -/
def NearDecideExact : Prop := ∀ b : Nat, Decides (nearControl b) (fun x => nearDecide (b,x))

/-- The joint near-control closed-block decision. -/
def UniformNearClosedBlockDecision : Prop :=
  ∃ decide : Nat × Args → Option Bool, Computable decide ∧
    ∀ b : Nat, Decides (nearControl b) (fun x => decide (b,x))

def FullUniformNearClosedBlock : Prop :=
  ParametricSolveEffectivity ∧ NearDecideComputable ∧ NearDecideExact ∧ UniformNearClosedBlockDecision

end LogicLineages.PermittedControl.UniformNearClosedBlock
