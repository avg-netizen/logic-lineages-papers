module
public import LogicLineages.OrdinalComparison.NumericCarrierDataTargets
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeSemanticProof
public import LogicLineages.OrdinalComparison.GroundCaptureClosingCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof
open ScalarAnnotationData

private theorem fresh_leaf (i j : Nat) : freshLeaf (8*Nat.pair i j+3) =
    8*Nat.pair (if i=0 then 0 else i+1) j+3 := by
  have hm : (8*Nat.pair i j+3)%8=3 := by omega
  have hd : (8*Nat.pair i j+3)/8=Nat.pair i j := by omega
  simp [freshLeaf,hm,hd]

theorem fresh_ordinal {Γ σ} (q : OrdinalExpression (σ::Γ)) :
    freshOrdinal (OrdinalSyntax.typedCode q) =
      OrdinalSyntax.typedCode (ordinalExpressionRename UnaryCarrier.renameTracked q) := by
  unfold freshOrdinal OrdinalSyntax.typedCode
  rw [OrdinalSyntax.ordinalSyntaxFoldCorrect]
  induction q with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x <;> simp [OrdinalSyntax.termFold,OrdinalSyntax.componentCode,fresh_leaf,
      SourceTypedPorts.variableIndex,UnaryCarrier.renameTracked,ordinalExpressionRename,ordinalComponentRename,
      OrdinalSyntax.code,ComputabilityKnowledge.WWOrdinalTermSemantics.substitute]
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | emul a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *
  | collapse a b iha ihb =>
    simp [OrdinalSyntax.termFold,iha,ihb,ordinalExpressionRename,
      ComputabilityKnowledge.WWOrdinalTermSemantics.substitute,OrdinalSyntax.code] at *

theorem fresh_vector {Γ σ m} (v : OrdinalVector (σ::Γ) m) :
    freshVector (OrdinalSyntax.vectorCode v) =
      OrdinalSyntax.vectorCode (SourceRenaming.renameVector UnaryCarrier.renameTracked v) := by
  simp only [freshVector,OrdinalSyntax.vectorCode,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact fresh_ordinal (v j)

theorem saturate_source {Γ} (r : Nat) (t : OriginalTerm Γ (Ty.curriedGround (r+1))) :
    saturateSource r (SyntaxCode.encodeTerm t) = SyntaxCode.encodeTerm (UnaryCarrier.saturate r t) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change saturateSource r (SyntaxCode.encodeTerm (Source.Term.app t .zeroC)) =
      SyntaxCode.encodeTerm (UnaryCarrier.saturate r (Source.Term.app t .zeroC))
    exact ih _

private theorem level_one (r : Nat) : (Ty.curriedGround (r+1)).level=1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change max 1 (Ty.curriedGround (r+1)).level=1
    rw [ih]
    rfl

theorem saturate_vector {Γ} (r : Nat) (v : OrdinalVector Γ (Ty.curriedGround (r+1)).level) :
    saturateVector r (OrdinalSyntax.vectorCode v) =
      OrdinalSyntax.vectorCode (DeterministicCarrierData.saturateVector r v) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    let z : OrdinalVector Γ Ty.ground.level := fun _ => .one
    let w := AdmissibleAssignment.application (σ := .ground) (τ := Ty.curriedGround (r+1))
      OrdinalSyntax.defaultPolicy v z
    have hz : OrdinalSyntax.vectorCode z=[1] := rfl
    have ha : OrdinalSyntax.defaultApplicationCode 1 0 (OrdinalSyntax.vectorCode v) [1] =
        OrdinalSyntax.vectorCode w := by
      calc
        _ = OrdinalSyntax.defaultApplicationCode (Ty.curriedGround (r+1)).level 0
            (OrdinalSyntax.vectorCode v) [1] :=
              congrArg (fun j => OrdinalSyntax.defaultApplicationCode j 0 (OrdinalSyntax.vectorCode v) [1]) (level_one r).symm
        _ = OrdinalSyntax.vectorCode w := by
          have h := OrdinalSyntax.defaultSyntaxApplicationCorrect Γ .ground (Ty.curriedGround (r+1)) v z
          rw [hz] at h
          exact h
    change saturateVector r (OrdinalSyntax.defaultApplicationCode 1 0 (OrdinalSyntax.vectorCode v) [1]) = _
    rw [ha]
    exact ih w

theorem exactCarrierCode : Targets.ExactCarrierCode := by
  intro k Γ op
  have hop := SourceAnnotationCode.Proof.exactOperatorCodec _ op
  unfold carrierCode
  rw [hop.1,hop.2.1,hop.2.2.1]
  simp only [List.map_cons,List.getD_cons_zero]
  rw [SourceCarrierMapCode.Proof.concreteExact.2 Γ (Ty.curriedGround (k+1)) _ op.source,
    fresh_vector,saturate_source,saturate_vector]
  have hs := GroundCaptureClosingCode.Proof.exactProtectedSource []
    (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ) _
    (UnaryCarrier.saturate op.arity (op.source.rename UnaryCarrier.renameTracked))
  have hv := GroundCaptureClosingCode.Proof.exactOrdinalVector.2
    (Ty.curriedGround (k+1)::Ty.curriedGround (k+1)::Γ) 1
    (DeterministicCarrierData.saturateVector op.arity (SourceRenaming.renameVector UnaryCarrier.renameTracked op.vector))
  simp only [List.map_cons,List.length_nil] at hs hv
  exact congrArg (Nat.pair 0) (congrArg₂ Nat.pair hs (congrArg Encodable.encode hv))
end LogicLineages.OrdinalComparison.Source.NumericCarrierData.Proof
