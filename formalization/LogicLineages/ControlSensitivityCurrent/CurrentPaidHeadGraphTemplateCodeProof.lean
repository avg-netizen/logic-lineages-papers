module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphLayoutProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRenameProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open CurrentUnitElimination (WireCtx shift OpenGraph groundWireCtx)
open RawSourceDAG (variableIndex)

private theorem lengthDirect (n : Nat) : (WireCtx n DirectCtx).length = n+2 := by
  rw [widthLength]
  rfl

private theorem lengthWire {Γ : List Ty} (w : Nat) : (WireCtx w (.ground::Γ)).length=w+1+Γ.length := by
  rw [widthLength,List.length_cons]
  omega

private theorem lengthRay {Γ : List Ty} (w : Nat) : (WireCtx w (.ground::.ground::Γ)).length=w+2+Γ.length := by
  rw [widthLength,List.length_cons,List.length_cons]
  omega

private theorem directBlockExact {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground)
    (δ nξ base : Nat) (small points : List Nat) (g : OpenGraph (.ground::Γ)) :
    directBlock Γ.length (Targets.blockCode g) δ nξ base small points =
      presentedCode (direct hg δ nξ base small points g) := by
  let wr := g.width
  let w := directWidth wr δ
  let Ξ := WireCtx w DirectCtx
  let Γr := WireCtx wr (.ground::.ground::Γ)
  let z : Variable Ξ .ground := shift w .here
  let hg' := groundWireCtx w DirectCtx directGround
  let hr := groundWireCtx wr (.ground::.ground::Γ) (groundCons (groundCons hg))
  let plan := route hr z (rayPlacement wr)
  have htab : (List.range (wr+2+Γ.length)).map (rayPlacement wr) =
      RawSourceDAG.Operations.renamingCode plan := by
    rw [← lengthRay (Γ:=Γ) wr]
    apply tableByIndex
    intro σ x
    symm
    apply indexRoute hr hg'
    change rayPlacement wr (variableIndex x)<Ξ.length
    rw [show Ξ.length=w+2 from lengthDirect w]
    unfold rayPlacement w directWidth
    split <;> omega
  have hm := MatrixCode.formulaRename plan g.matrix
  rw [allGroundMap Ξ hg',show Ξ.length=w+2 from lengthDirect w,← htab] at hm
  have he := (codeLayout hg' z).wholePart wr δ nξ base (show directWidth wr δ+1<Ξ.length by
      rw [show Ξ.length=w+2 from lengthDirect w]; omega) small points
    (CurrentUnitElimination.renameFormula plan g.matrix)
  change (w,directBody rawLayout wr δ nξ base small points
    (MatrixCode.renameFormula (UnitCode.bitCtx (w+2)) _ (MatrixCode.formula g.matrix))) =
    (w,MatrixCode.formula (directBody (typedLayout z) wr δ nξ base small points
      (CurrentUnitElimination.renameFormula plan g.matrix)))
  rw [he]
  exact congrArg (fun q => (w,directBody rawLayout wr δ nξ base small points q)) hm

private theorem insertBlockExact {Γ : List Ty} (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat)
    (b c : OpenGraph Γ) (g : Presented DirectCtx) :
    insertedBlock Γ.length nξ level (Targets.blockCode b) (Targets.blockCode c) (presentedCode g) =
      presentedCode (inserted hg nξ level b c g) := by
  let wb := b.width
  let wc := c.width
  let wg := g.width
  let w := insertedWidth wb wc wg
  let Ξ := WireCtx w (.ground::Γ)
  let z : Variable Ξ .ground := shift w .here
  let hΞ := groundWireCtx w (.ground::Γ) (groundCons hg)
  let hB := groundWireCtx wb (.ground::Γ) (groundCons hg)
  let hC := groundWireCtx wc (.ground::Γ) (groundCons hg)
  let hG := groundWireCtx wg DirectCtx directGround
  let rB := route hB z (placeB wb wc wg)
  let rC := route hC z (placeC wb wc wg)
  let rG := route hG z (placeGraph wb wc wg)
  have htabB : (List.range (wb+1+Γ.length)).map (placeB wb wc wg) =
      RawSourceDAG.Operations.renamingCode rB := by
    rw [← lengthWire (Γ:=Γ) wb]
    apply tableByIndex
    intro σ x
    have hbound := indexBound x
    rw [lengthWire] at hbound
    symm
    apply indexRoute hB hΞ
    change placeB wb wc wg (variableIndex x)<Ξ.length
    rw [lengthWire]
    unfold placeB w insertedWidth operandEnd
    split <;> try split <;> omega
  have htabC : (List.range (wc+1+Γ.length)).map (placeC wb wc wg) =
      RawSourceDAG.Operations.renamingCode rC := by
    rw [← lengthWire (Γ:=Γ) wc]
    apply tableByIndex
    intro σ x
    have hbound := indexBound x
    rw [lengthWire] at hbound
    symm
    apply indexRoute hC hΞ
    change placeC wb wc wg (variableIndex x)<Ξ.length
    rw [lengthWire]
    unfold placeC w insertedWidth operandEnd
    split <;> try split <;> omega
  have htabG : (List.range (wg+2)).map (placeGraph wb wc wg) =
      RawSourceDAG.Operations.renamingCode rG := by
    rw [← lengthDirect wg]
    apply tableByIndex
    intro σ x
    have hbound := indexBound x
    rw [lengthDirect] at hbound
    symm
    apply indexRoute hG hΞ
    change placeGraph wb wc wg (variableIndex x)<Ξ.length
    rw [lengthWire]
    unfold placeGraph w insertedWidth operandEnd
    split <;> omega
  have hctx : Ξ.map SyntaxCode.typeCode=UnitCode.bitCtx (w+1+Γ.length) := by
    rw [allGroundMap Ξ hΞ,lengthWire]
    rfl
  have hb := MatrixCode.formulaRename rB b.matrix
  have hc := MatrixCode.formulaRename rC c.matrix
  have hh := MatrixCode.formulaRename rG g.matrix
  rw [hctx,← htabB] at hb
  rw [hctx,← htabC] at hc
  rw [hctx,← htabG] at hh
  have he := (codeLayout hΞ z).splicePart wb wc wg nξ level (show operandEnd wb wc wg+2<Ξ.length by
      rw [lengthWire]; unfold w insertedWidth; omega)
    (CurrentUnitElimination.renameFormula rB b.matrix)
    (CurrentUnitElimination.renameFormula rC c.matrix) (CurrentUnitElimination.renameFormula rG g.matrix)
  change (w,insertedBody rawLayout wb wc wg nξ level _ _ _) =
    (w,MatrixCode.formula (insertedBody (typedLayout z) wb wc wg nξ level _ _ _))
  rw [he,hb,hc,hh]

theorem exactTemplateCodes : Targets.ExactTemplateCodes :=
  ⟨fun _ hg => directBlockExact hg, fun _ hg => insertBlockExact hg⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
