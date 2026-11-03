module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeTargets
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.ActualOrdinalNorm
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Proof
open BalancedSyntax BalancedEvaluation

private theorem getDOfFn {A : Type} {k : Nat} (f : Fin k → A) (d : A)
    (j : Nat) (hj : j < k) : (List.ofFn f).getD j d = f ⟨j,hj⟩ := by
  rw [List.getD_eq_getElem _ d (by simpa using hj)]
  simp only [List.getElem_ofFn]

private theorem mapRangeFin {A : Type} (k : Nat) (f : Nat → A) (g : Fin k → A)
    (h : ∀ j (hj : j < k), f j = g ⟨j,hj⟩) :
    (List.range k).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact h i (by simpa using hi)

private theorem numeralExact (Γ : List Nat) (n : Nat) :
    numeral Γ n = encodeSyntax Γ (Affine.numeral Γ n) := by
  cases Γ with
  | nil => rfl
  | cons k Γ =>
      simp only [numeral,Affine.numeral,encodeSyntax,List.ofFn_const,List.map_nil]

/-- The complete ordered encoded atom list is retained, not merely its value
or support. In particular, duplicate atoms and their coefficients survive. -/
private theorem addExact (Γ : List Nat) (E F : Syntax Γ) :
    add Γ (encodeSyntax Γ E) (encodeSyntax Γ F) =
      encodeSyntax Γ (Affine.add Γ E F) := by
  cases Γ with
  | nil => rfl
  | cons k Γ =>
      have hout : (List.range k).map
          (fun j => (List.ofFn E.outside).getD j 0 + (List.ofFn F.outside).getD j 0) =
          List.ofFn (fun j => E.outside j + F.outside j) := by
        apply mapRangeFin
        intro j hj
        rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj]
      simp only [add,upperData,encodeSyntax,Encodable.encodek,Option.getD_some,
        Affine.add,List.map_append,hout]

private theorem foldExact (Γ : List Nat) (Es : List (Syntax Γ)) :
    (Es.map (encodeSyntax Γ)).foldr (add Γ) (numeral Γ 0) =
      encodeSyntax Γ (Es.foldr (Affine.add Γ) (Affine.numeral Γ 0)) := by
  induction Es with
  | nil => exact numeralExact Γ 0
  | cons E Es ih =>
      simp only [List.map_cons,List.foldr_cons,ih,addExact]

private theorem scaleExact (Γ : List Nat) (n : Nat) (E : Syntax Γ) :
    scale Γ n (encodeSyntax Γ E) = encodeSyntax Γ (Affine.scale Γ n E) := by
  simpa only [scale,Affine.scale,List.map_replicate] using
    foldExact Γ (List.replicate n E)

theorem exactLiteralOperations : Targets.ExactLiteralOperations := by
  intro Γ
  exact ⟨numeralExact Γ,addExact Γ,scaleExact Γ⟩

theorem exactFiniteCombination : Targets.ExactFiniteCombination := by
  intro Γ k c coefficients basis
  have hterms : (List.range k).map
      (fun j => scale Γ ((List.ofFn coefficients).getD j 0)
        ((List.ofFn (fun i => encodeSyntax Γ (basis i))).getD j 0)) =
      (List.ofFn (fun j => Affine.scale Γ (coefficients j) (basis j))).map
        (encodeSyntax Γ) := by
    rw [List.map_ofFn]
    apply mapRangeFin
    intro j hj
    rw [getDOfFn _ _ j hj,getDOfFn _ _ j hj,scaleExact]
    rfl
  unfold combination Affine.combination
  rw [hterms,foldExact,numeralExact,addExact]

theorem exactActualLowerAndInputs : Targets.ExactActualLowerAndInputs := by
  intro k Γ C E a q
  constructor
  · simp only [lowerPart,upperData,encodeSyntax,encodeCertificate,certificateData,
      Encodable.encodek,Option.getD_some,Affine.lowerPart]
    exact exactFiniteCombination Γ k E.constant E.outside C.2
  · have hnorm : rawNormCode (rawNoteEncode a.head.1) =
        actualOrdinalNorm a.head.1.repr :=
      (rawNormCodeCorrect a.head.1).trans
        (actualOrdinalNorm_notationCorrespondence a.head).symm
    have hfactors : (List.range k).map
        (fun j => (List.ofFn a.factors).getD j 0 + 1) =
        List.ofFn (fun j => a.factors j + 1) := by
      apply mapRangeFin
      intro j hj
      rw [getDOfFn _ _ j hj]
    simp only [completeInput,atomData,encodeAtom,encodeCertificate,certificateData,
      Encodable.encodek,Option.getD_some,Affine.completeInput,hnorm,hfactors]
    exact exactFiniteCombination Γ k (actualOrdinalNorm a.head.1.repr + a.offset)
      (fun j => a.factors j + 1) C.2

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCode.Proof
