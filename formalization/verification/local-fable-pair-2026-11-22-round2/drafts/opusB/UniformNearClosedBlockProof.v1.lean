module
public import LogicLineages.PermittedControl.UniformNearClosedBlockTargets
import LogicLineages.PermittedControl.UniformNearClosedBlockDriverProof
import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendPrimitiveProof
import LogicLineages.PermittedControl.ActualRawStageCutoffPrimitiveProof
import LogicLineages.PermittedControl.EffectivityProof
import LogicLineages.PermittedControl.StageEmitterGuardProof
import LogicLineages.PermittedControl.StageEmitterHighProof
import LogicLineages.PermittedControl.StageCallbackGuardRenderCloseProof
import LogicLineages.PermittedControl.StageCallbackLevelOrderProof
import LogicLineages.PermittedControl.StageCallbackSupplierStatementChecks
import LogicLineages.PermittedControl.OriginalPrintedRawSelectedStageQueryStatementChecks

public section
namespace LogicLineages.PermittedControl.UniformNearClosedBlock
open ClosedBlockDecision (Decides)
open OriginalPrintedRawFamilyFrontend (Args familyCode originalRawFamilyFrontendEffectivity)
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawDriver (solve)
open ActualRawStageCutoff (stageBound stageBoundPrimitive)
open StageCallbackLevelOrder (levelOrder exactLevelOrderSupplierShape exactLevelOrderSupplierExact)
open StageCallbackSupplier (stageChildren)

theorem nearRenderingExact : nearRendering.Exact ∧ StageEmitter.RenderingEffective nearRendering :=
  StageEmitter.exactRenderingFromGuard StageCallbackGuardRender.guardCode
    StageCallbackGuardRender.guardExact StageCallbackGuardRender.guardEffective

theorem nearDecideComputable : NearDecideComputable := by
  have hh : Computable (StageEmitter.highCode nearRendering) :=
    (StageEmitter.exactHighCodeEffectivity nearRendering nearRenderingExact.2).2
  have hF : Computable₂ nearControl := nearControl_primrec.to_comp
  have hb : Computable₂ (fun (b : Nat) (raw : RawFamily) => stageBound (b + 1) raw) :=
    (stageBoundPrimitive.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to_comp
  have hs := solveParam nearControl (fun b raw => stageBound (b + 1) raw)
    (StageEmitter.highCode nearRendering) hF hb hh
  have front : Computable (fun x : Nat × Args => familyCode x.2) :=
    (show Primrec familyCode from originalRawFamilyFrontendEffectivity).to_comp.comp Computable.snd
  have post : Computable₂ (fun (x : Nat × Args) (raw : RawFamily) =>
      solve (nearControl x.1) (fun r => stageBound (x.1 + 1) r) (StageEmitter.highCode nearRendering) raw) := by
    have h := hs.comp ((Computable.fst.comp (Computable.fst : Computable (Prod.fst : (Nat × Args) × RawFamily → Nat × Args))).pair
      (Computable.snd : Computable (Prod.snd : (Nat × Args) × RawFamily → RawFamily)))
    exact h.to₂
  have h := Computable.option_map front post
  exact h.of_eq (fun _ => rfl)

theorem nearDecideExact : NearDecideExact := by
  intro b
  have selected : SelectedWithThreshold (nearControl b) (b + 1) := Or.inr ⟨b,rfl,rfl⟩
  have control := StatementChecks.fixed_exactOriginalRawSelectedStageQuery.2 b
  have stage := StatementChecks.fixed_exactSuppliedStageCallback (nearControl b) (b + 1) levelOrder
    exactLevelOrderSupplierShape (exactLevelOrderSupplierExact (nearControl b) (b + 1) selected)
    (StageEmitter.highCode nearRendering) (StageEmitter.exactStageEmission nearRendering nearRenderingExact.1 (b + 1))
  exact control.1 (StageEmitter.highCode nearRendering) (stageChildren levelOrder (b + 1)) stage

theorem uniformNearClosedBlockDecision : UniformNearClosedBlockDecision :=
  ⟨nearDecide,nearDecideComputable,nearDecideExact⟩

theorem fullUniformNearClosedBlock : FullUniformNearClosedBlock :=
  ⟨parametricSolveEffectivity,nearDecideComputable,nearDecideExact,uniformNearClosedBlockDecision⟩

#print axioms nearDecideComputable
#print axioms nearDecideExact
#print axioms uniformNearClosedBlockDecision
#print axioms fullUniformNearClosedBlock

end LogicLineages.PermittedControl.UniformNearClosedBlock
