module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundSourceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
open ScalarCarrierAccounting
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem rename_identity {Γ} (q : OrdinalExpression Γ) :
    ordinalExpressionRename (fun x => x) q = q := by
  induction q with
  | var c => rfl
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    change _ = _
    simp only [ordinalExpressionRename,substitute] at iha ihb ⊢
    rw [iha,ihb]

theorem actualSourceLowerBound : Targets.ActualSourceLowerBound := by
  intro k Γ n e
  obtain ⟨u,v,hu,hv,hex,hsem⟩ := AccountSemanticDeterminacy.Proof.actualSourceSoundness k Γ n e
  refine ⟨u,hu,hex,?_⟩
  intro xs c hac
  have hh := renamedSourceLowerBound k (Ty.curriedGround (k+1) :: Γ) Γ .here n e u
    (fun x => x) (fun _ => Function.injective_id) rfl hu xs c
  rw [rename_identity] at hh
  exact hh hac
end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
