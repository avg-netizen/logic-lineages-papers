module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphDirectFiberProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison.Source
open AdmissibleSum
open RawSourceDAG (variableIndex)
open CurrentUnitElimination (WireCtx shift OpenGraph HoldsRaw groundWireCtx)

private theorem widthOne (w : Nat) (Γ : List Ty) : (WireCtx w (.ground::Γ)).length=w+1+Γ.length := by
  rw [widthLength,List.length_cons]; omega

private theorem frameLimit (wb wc wg : Nat) (Γ : List Ty) :
    let width := insertedWidth wb wc wg
    let Ξ := WireCtx width (.ground::Γ)
    (∀ i<wb+1+Γ.length, placeB wb wc wg i < Ξ.length) ∧
    (∀ i<wc+1+Γ.length, placeC wb wc wg i < Ξ.length) ∧
    (∀ i<wg+2, placeGraph wb wc wg i < Ξ.length) := by
  dsimp only
  simp only [widthOne]
  refine ⟨?_,?_,?_⟩
  · intro i hi
    unfold placeB insertedWidth operandEnd
    split <;> try split <;> omega
  · intro i hi
    unfold placeC insertedWidth operandEnd
    split <;> try split <;> omega
  · intro i hi
    unfold placeGraph insertedWidth operandEnd
    split <;> omega

/-- Open splice fiber in the actual positional coordinates. The one common
external valuation is fixed once, and each original source matrix is pulled
back from that same typed combined witness. -/
theorem insertedFiber (p : Policy) (f : Nat→Nat) {Γ : List Ty}
    (hg : ∀ σ ∈ Γ, σ = .ground) (nξ level : Nat) (b c : OpenGraph Γ) (g : Presented DirectCtx)
    (ρ : Variable Γ .ground→Nat) (y : Nat) :
    (inserted hg nξ level b c g).holds p f (resultValues ρ y) ↔
      ∃ w : Nat→Nat,
        let i := operandEnd b.width c.width g.width
        let n := insertedWidth b.width c.width g.width
        (∀ x : Variable (.ground::Γ) .ground, w (n+variableIndex x)=resultValues ρ y x) ∧
        b.matrix.eval p f (byIndex (fun j => w (placeB b.width c.width g.width j)))=true ∧
        c.matrix.eval p f (byIndex (fun j => w (placeC b.width c.width g.width j)))=true ∧
        w (i+2)=nξ+level+2+w i+w (i+1) ∧
        g.matrix.eval p f (byIndex (fun j => w (placeGraph b.width c.width g.width j)))=true := by
  let bb := b.width
  let cc := c.width
  let gg := g.width
  let i := operandEnd bb cc gg
  let n := insertedWidth bb cc gg
  let Ξ := WireCtx n (.ground::Γ)
  let z : Variable Ξ .ground := shift n .here
  let hΞ := groundWireCtx n _ (groundCons hg)
  let hB := groundWireCtx bb _ (groundCons hg)
  let hC := groundWireCtx cc _ (groundCons hg)
  let hG := groundWireCtx gg _ directGround
  have HL := frameLimit bb cc gg Γ
  let PB := placeB bb cc gg
  let PC := placeC bb cc gg
  let PG := placeGraph bb cc gg
  have e (ν : Variable Ξ .ground→Nat) (w : Nat→Nat) (H : ∀ j<Ξ.length, ν (slot z j)=w j) :
      (inserted hg nξ level b c g).matrix.eval p f ν=true ↔
        b.matrix.eval p f (byIndex (fun j => w (PB j)))=true ∧
        c.matrix.eval p f (byIndex (fun j => w (PC j)))=true ∧
        w (i+2)=nξ+level+2+w i+w (i+1) ∧
        g.matrix.eval p f (byIndex (fun j => w (PG j)))=true := by
    let B := CurrentUnitElimination.renameFormula (route hB z PB) b.matrix
    let C := CurrentUnitElimination.renameFormula (route hC z PC) c.matrix
    let G := CurrentUnitElimination.renameFormula (route hG z PG) g.matrix
    have H₁ : i<Ξ.length := by rw [widthOne]; unfold n insertedWidth; omega
    have H₂ : i+1<Ξ.length := by omega
    have H₃ : i+2<Ξ.length := by rw [widthOne]; unfold n insertedWidth; omega
    change (insertedBody (typedLayout z) bb cc gg nξ level B C G).eval p f ν=true ↔ _
    have EB := indexedPull hB hΞ z PB ν w H (fun j hj => by rw [widthOne] at hj; exact HL.1 j hj) p f b.matrix
    have EC := indexedPull hC hΞ z PC ν w H (fun j hj => by rw [widthOne] at hj; exact HL.2.1 j hj) p f c.matrix
    have EG := indexedPull hG hΞ z PG ν w H (fun j hj =>
      have h : j<gg+2 := by simpa only [widthLength,DirectCtx,List.length_cons,List.length_nil] using hj
      exact HL.2.2 j h) p f g.matrix
    simp only [insertedBody,typedLayout,SourceAST.Formula.eval,SourceAST.Term.eval,Bool.and_eq_true,
      decide_eq_true_eq,i,H _ H₁,H _ H₂,H _ H₃,B,C,G,EB,EC,EG]
    tauto
  constructor
  · rintro ⟨ν,hρ,hM⟩
    let w := fun j => ν (slot z j)
    refine ⟨w,?_,(e ν w (fun _ _ => rfl)).mp hM⟩
    intro x
    change ν (slot z (n+variableIndex x)) = _
    rw [← shiftedIndex n x,slotAt]
    exact hρ x
  · rintro ⟨w,hρ,hM⟩
    let ν : Variable Ξ .ground→Nat := byIndex w
    refine ⟨ν,?_,(e ν w (fun _ hj => congrArg w (indexSlot hΞ z hj))).mpr hM⟩
    intro x
    change w (variableIndex (shift n x)) = _
    rw [shiftedIndex]
    exact hρ x

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
