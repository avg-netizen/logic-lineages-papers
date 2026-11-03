module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceSelectionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxDescentProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceTargets
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax

private theorem sourceAtomShape (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (ν : Nat → Nat) (a : Atom k) :
    (asAtom a).coefficients.length = (basisValues k Γ C ν).length ∧
      ∀ c ∈ (asAtom a).coefficients, 1 ≤ c := by
  constructor
  · simp [asAtom, basisValues]
  · intro c hc
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
    omega

private theorem sourceRowWellFormed (k : Nat) (Γ : List Nat)
    (C : Certificate (k::Γ)) (E F : Upper k) (ν : Nat → Nat) :
    BalancedRow.wellFormed (basisValues k Γ C ν) (comparisonRow E F) := by
  constructor
  · simp [comparisonRow, basisValues]
  · intro a ha
    rcases List.mem_append.mp ha with he | hf
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
      exact sourceAtomShape k Γ C ν b.2
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
      exact sourceAtomShape k Γ C ν b.2

private theorem sourceRowGenuine (k : Nat) (Γ : List Nat) (E F : Upper k)
    (hE : genuineExpression (k::Γ) E) (hF : genuineExpression (k::Γ) F) :
    BalancedRow.genuineHeads (comparisonRow E F) := by
  intro a ha
  rcases List.mem_append.mp ha with he | hf
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
    exact hE b hb
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hf
    exact hF b hb

private theorem sourceZipNatCast (rs : List Int) (bs : List Nat) :
    rs.zipWith (fun r b => r*(b:Int)) bs =
      rs.zipWith (fun (r:Int) (b:Nat) => r*(b:Int)) bs := by
  induction rs generalizing bs with
  | nil => rfl
  | cons r rs ih =>
    cases bs with
    | nil => rfl
    | cons b bs =>
      change r*(b:Int)::(rs.zipWith (fun r b => r*(b:Int)) bs) =
        r*(b:Int)::(rs.zipWith (fun (r:Int) (b:Nat) => r*(b:Int)) bs)
      rw [ih]

private theorem sourceCastSumOfFn (k : Nat) : ∀ f : Fin k → Nat,
    ((List.ofFn f).sum:Int) = (List.ofFn (fun j => (f j:Int))).sum := by
  induction k with
  | zero => intro f; rfl
  | succ k ih =>
    intro f
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [List.sum_cons, Nat.cast_add, ih]

private theorem sourceSubSumOfFn (k : Nat) : ∀ f g : Fin k → Int,
    (List.ofFn (fun j => f j-g j)).sum = (List.ofFn f).sum-(List.ofFn g).sum := by
  induction k with
  | zero => intro f g; rfl
  | succ k ih =>
    intro f g
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp only [List.sum_cons, ih]
    ring

private theorem sourceOutsideDifference {k : Nat} (a b v : Fin k → Nat) :
    ((List.ofFn (fun j => (a j:Int)-(b j:Int))).zipWith
      (fun (r:Int) (x:Nat) => r*(x:Int)) (List.ofFn v)).sum =
      (((List.ofFn a).zipWith (fun (x y:Nat) => (x*y:Nat)) (List.ofFn v)).sum:Int)-
      (((List.ofFn b).zipWith (fun (x y:Nat) => (x*y:Nat)) (List.ofFn v)).sum:Int) := by
  rw [Affine.Proof.affineZipOfFn, Affine.Proof.affineZipOfFn,
    Affine.Proof.affineZipOfFn, sourceCastSumOfFn, sourceCastSumOfFn]
  have ht : (fun j : Fin k => ((a j:Int)-(b j:Int))*(v j:Int)) =
      (fun j => ((a j*v j:Nat):Int)-((b j*v j:Nat):Int)) := by
    funext j
    simp only [Nat.cast_mul]
    ring
  simpa only [ht, sourceSubSumOfFn]

private theorem sourceCastSumMap {A : Type} (xs : List A) (f : A → Nat) :
    ((xs.map f).sum:Int) = (xs.map (fun a => (f a:Int))).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

private theorem sourceNegSumMap {A : Type} (xs : List A) (f : A → Int) :
    (xs.map (fun a => -(f a))).sum = -(xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

private theorem sourceCastHeadSum {k : Nat} (E : Upper k) (basis : List Nat) :
    ((E.atoms.map (fun a => (a.1+1)*actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)))).sum:Int) =
    (E.atoms.map (fun a => (a.1+1:Int)*(actualHeadValue a.2.head.1.repr
      (BalancedRow.input basis (asAtom a.2)):Int))).sum := by
  rw [sourceCastSumMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

private theorem sourceAtomHead {k : Nat} (a : Atom k) : (asAtom a).head = a.head := rfl

/-- Direct calibration keeps the original certificate, basis and valuation;
only elementary list arithmetic is used for the signed source row. -/
private theorem sourceComparisonRow (k : Nat) (Γ : List Nat) (C : Certificate (k::Γ))
    (E F : Upper k) (ν : Nat → Nat) :
    BalancedRow.value (basisValues k Γ C ν) (comparisonRow E F) =
      (value (k::Γ) C E ν:Int)-(value (k::Γ) C F ν:Int) := by
  simp only [value, basisValues]
  unfold BalancedRow.value BalancedRow.remainderValue comparisonRow
  rw [sourceZipNatCast, sourceOutsideDifference]
  simp only [List.map_append, List.map_map, List.sum_append, Function.comp_def,
    sourceAtomHead, neg_mul]
  rw [sourceNegSumMap]
  simp only [Nat.cast_add]
  rw [sourceCastHeadSum, sourceCastHeadSum]
  ring

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSyntax

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Proof

/-- The original signed source pair either cancels to its two actual lower
parts or every greatest surviving actual key gives its sign. The threshold
premise is tested before collection on the same original row. -/
theorem actualSourceDichotomy : Targets.ActualSourceDichotomy := by
  intro k Γ C E F ν hE hF hlarge
  have hw := BalancedSyntax.sourceRowWellFormed k Γ C E F ν
  have hg := BalancedSyntax.sourceRowGenuine k Γ E F hE hF
  have hv := BalancedSyntax.sourceComparisonRow k Γ C E F ν
  rcases actualCollectedDichotomy (BalancedSyntax.basisValues k Γ C ν)
    (BalancedSyntax.comparisonRow E F) hw hg hlarge with
    hc | ⟨winner, hwinner, hne, hsign⟩
  · exact Or.inl ⟨hc.1,
      BalancedSyntax.Affine.Proof.actualCanceledDescent k Γ C E F ν hc.1⟩
  · refine Or.inr ⟨⟨winner, hwinner⟩, ?_⟩
    intro other hother
    have hs := everyGreatestSurvivorSign (BalancedSyntax.basisValues k Γ C ν)
      (BalancedSyntax.comparisonRow E F) hw hg hlarge other hother
    exact ⟨hs.1, by rw [← hv]; exact hs.2⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.CollectedDominance.Proof
