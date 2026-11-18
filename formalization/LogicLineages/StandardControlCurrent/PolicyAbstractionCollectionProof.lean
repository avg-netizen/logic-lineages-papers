module
public import LogicLineages.StandardControlCurrent.PolicyAbstractionTargets
public import LogicLineages.StandardControlCurrent.PolicyPartialSyntaxProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAbstractionCollectionProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
theorem collect_codes {α : Type} (n : Nat) (f : Fin n → Option α) (enc : α → List Nat) :
    collectLists (List.ofFn (fun i => (f i).map enc)) =
      (AdmissibleAssignment.collect n f).map (fun v => List.ofFn (fun i => enc (v i))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ, collectLists, AdmissibleAssignment.collect]
    rw [ih]
    cases hf : f 0 <;> cases hr : AdmissibleAssignment.collect n (fun i => f i.succ) <;>
      simp [List.ofFn_succ]

theorem range_map {α : Type} (n : Nat) (f : Nat → α) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk; simp

theorem lookup {n : Nat} (f : Fin n → Nat) (j : Fin n) :
    (List.ofFn f).getD j.val 0 = f j := by
  simp [List.getD_eq_getElem?_getD, j.isLt]

theorem partials : PolicyAbstractionTargets.PartialsCalibration := by
  intro p Γ σ m h
  unfold PolicyAbstraction.partialsCode
  rw [range_map]
  have hi : (fun i : Fin (m+1) => PolicyPartial.run p σ.level i.val ((vectorCode h).getD i.val 0)) =
      (fun i => (AdmissiblePartial.run p i.val (h i)).map
        (fun v => List.ofFn (fun j => typedCode (v j)))) := by
    funext i
    rw [show (vectorCode h).getD i.val 0 = typedCode (h i) from lookup _ i]
    exact PolicyPartialSyntaxProof.literal p Γ σ i.val (h i)
  rw [hi]
  exact collect_codes _ _ _

theorem factor : PolicyAbstractionTargets.FactorCalibration := by
  intro Γ σ m h
  unfold PolicyAbstraction.factorCode
  congr 2
  simp only [vectorCode,List.map_ofFn]
  congr 1
  funext i
  exact ordinalSyntaxPartialSizeCorrect Γ σ (h i)
end LogicLineages.StandardControlCurrent.PolicyAbstractionCollectionProof
