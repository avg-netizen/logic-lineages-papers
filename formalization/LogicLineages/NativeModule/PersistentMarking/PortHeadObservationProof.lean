module

public import LogicLineages.NativeModule.PersistentMarking.PortNormalizationTargets
public import LogicLineages.NativeModule.PersistentMarking.ObservationLambdaProof

@[expose] public section

namespace LogicLineages.PersistentMarking.PortHeadObservationProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations PortNormalization

theorem headReflection (vs : Args) (q : Expr) (f : Head) (bs : Args) (hv : ObservationLambda.FreeValues vs)
    (h : openOccurrence vs q = .head f bs) : ∃ original, q = .head f original ∧ bs = substituteArgs vs 0 original := by
  cases q with
  | free τ y => cases h
  | bound τ i =>
    cases hl : vs.get i with
    | none => simp [openOccurrence,substitute,hl] at h
    | some v => obtain ⟨υ,y,rfl⟩ := hv i v hl; simp [openOccurrence,substitute,hl,shift] at h
  | lam τ q => cases h
  | head g qs =>
    simp only [openOccurrence,substitute,Expr.head.injEq] at h
    obtain ⟨rfl,hb⟩ := h
    exact ⟨qs,rfl,hb.symm⟩
  | marked g τ qs es => cases h

theorem atSubstitution (vs : Args) (d : Nat) (qs : Args) (i : Nat) (r : Expr)
    (h : At (substituteArgs vs d qs) i r) : ∃ q, At qs i q ∧ r = substitute vs d q := by
  cases qs with
  | nil => cases h
  | cons q qs => cases h with
    | here => exact ⟨q,.here,rfl⟩
    | there h => obtain ⟨q,hq,hr⟩ := atSubstitution vs d qs _ r h; exact ⟨q,.there hq,hr⟩
termination_by sizeOf qs

theorem atOccurrence (stack : List Ty) (qs : Args) (i : Nat) (q : Expr) (h : At qs i q) : OccursArgs stack qs stack q := by
  induction h with
  | here => exact .here .root
  | there h ih => exact .there ih

theorem atDepth (qs : Args) (i : Nat) (q : Expr) (h : At qs i q) : lambdaDepth q ≤ lambdaDepthArgs qs := by
  induction h with
  | here => exact Nat.le_max_left _ _
  | there h ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem headObservations : PortNormalizationTargets.HeadObservations := by
  intro S F Γ f bs hw hobs i r hat
  obtain ⟨stack,q,vs,hocc,hvs,hqtype,hdepth,heq⟩ :=
    (DecisionObservationProof.enumeration F.data.names F.data.ports Γ F.target (Expr.head f bs).type (.head f bs)).mp hobs
  have hv : ObservationLambda.FreeValues vs := DecisionAssignmentProof.freeValues F.data.names Γ stack vs hvs
  obtain ⟨original,rfl,hbs⟩ := headReflection vs q f bs hv heq.symm
  rw [hbs] at hat
  obtain ⟨child,hchild,rfl⟩ := atSubstitution vs 0 original i r hat
  have hc : Occurs [] F.target stack child :=
    ObservationLambdaProof.occurrenceTrans [] F.target stack (.head f original) hocc stack child (.head (atOccurrence stack original i child hchild))
  have hct := DecisionOccurrenceProof.typed [] F.target F.targetType stack child F.targetPaper.1 hc
  have hout := DecisionAssignmentProof.openingTyped F.data.names Γ stack vs child child.type hvs hct
  have ha : (substitute vs 0 child).type = child.type := SpineShiftProof.annotationExact _ _ _ hout
  have hd := atDepth original i child hchild
  apply (DecisionObservationProof.enumeration F.data.names F.data.ports Γ F.target (substitute vs 0 child).type _).mpr
  refine ⟨stack,child,vs,hc,hvs,ha.symm,?_,rfl⟩
  change lambdaDepthArgs original + used Γ ≤ F.data.ports at hdepth
  omega
end LogicLineages.PersistentMarking.PortHeadObservationProof
