module
public import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionTargets
import LogicLineages.PermittedControl.PolicyIndexedGroundDecisionSemanticProof
import LogicLineages.PermittedControl.PolicyIndexedGroundDriverCalibrationProof
import LogicLineages.PermittedControl.PolicyIndexedGroundDriverProgramsProof
import LogicLineages.PermittedControl.StageCallbackGuardRenderCloseProof
import LogicLineages.StandardControlCurrent.PolicyIndexedDeciderSpecializationProof

public section
namespace LogicLineages.PermittedControl.PolicyIndexedGroundDriver
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax Source.ForwardTranslation
open SelectedSourceDomain SelectedGeneratedSource
open GroundComparison (Relation)
open GroundComparisonAssembly (QueryInterface)
open ClosedBlockDecision (DecidableClosedBlocks)
open StandardControlCurrent.PolicyIndexedDeciderSpecialization (jointProgramIndexSpecialization)
open Nat.Partrec (Code)

private theorem indexedGroundOf (src : IndexedSource) (hs : Partrec src) (he : SourceExact src)
    (query : Query) (hq : QueryInterface query)
    (hqc : Computable (fun x : TermInput => query x.1 x.2.1 x.2.2))
    (ctrl : Nat → Nat) (K : Nat) (hsel : SelectedWithThreshold ctrl K)
    (hcb : DecidableClosedBlocks ctrl) : IndexedGroundDecidable ctrl := by
  intro rel
  obtain ⟨cbd,hcbd,hdec⟩ := hcb
  let f : IndexedInput → Part Bool := indexedDecision src cbd query rel
  have hf : Partrec f := indexedDecisionPartrec src hs cbd hcbd query hqc rel
  let joint : Nat → Part Nat := fun n =>
    (Encodable.decode (α := IndexedInput) n : Part IndexedInput).bind
      (fun x => (f x).map Encodable.encode)
  have hj : Nat.Partrec joint := hf
  obtain ⟨compile,hprim,hcomp⟩ := jointProgramIndexSpecialization joint hj
  refine ⟨compile,hprim,?_⟩
  intro e p hcode Γ hΓ τ υ a b
  let x : TermInput := (Γ.length,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  refine ⟨pointwiseDecision p cbd query rel x, ?_, ?_⟩
  · change Code.eval (compile e) (Encodable.encode x) = _
    rw [hcomp e (Encodable.encode x), ← Encodable.encode_prod_val e x]
    unfold joint
    rw [Encodable.encodek]
    change ((f (e,x)).map Encodable.encode) = _
    rw [show f (e,x) = Part.some (pointwiseDecision p cbd query rel x)
      from exactIndexedDecision src he cbd query rel e p hcode x]
    rfl
  · exact pointwiseDecisionCorrect query hq ctrl K hsel p rel cbd
      (fun known gs pf ht hp flag => (hdec known gs pf ht hp flag).1)
      Γ hΓ τ υ a b

theorem indexedGroundFromSourceAndQuery : IndexedGroundFromSourceAndQuery := by
  intro src hs he query hq hqc
  have cbd := StageCallbackGuardRender.closedBlockDecision
  exact ⟨indexedGroundOf src hs he query hq hqc _ 0 (Or.inl ⟨rfl,rfl⟩) cbd.1,
    fun b => indexedGroundOf src hs he query hq hqc _ (b+1) (Or.inr ⟨b,rfl,rfl⟩) (cbd.2 b)⟩

#print axioms indexedGroundFromSourceAndQuery
end LogicLineages.PermittedControl.PolicyIndexedGroundDriver
