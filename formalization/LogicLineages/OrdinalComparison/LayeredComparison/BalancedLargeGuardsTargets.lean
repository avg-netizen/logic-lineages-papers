module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Targets

/-- Fixed heads use actual ordinal identity/order. Masks sum exactly the
signed coefficients of one equal-head, equal-complete-input block. -/
def ExactHeadAwareBlocks : Prop := ∀ (heads : Nat → NONote) (ν : Nat → Nat),
  (∀ i j, (keyEqualFormula heads i j).eval ν ↔
    (heads i).1.repr = (heads j).1.repr ∧ ν i = ν j) ∧
  (∀ i j, (keyLessFormula heads i j).eval ν ↔
    actualHeadKeyLess (heads i).1.repr (ν i) (heads j).1.repr (ν j)) ∧
  (∀ (cs : List Int) (i : Nat) (desired : Int),
    (blockFormula heads cs i desired).eval ν ↔
      Int.sign (blockCoefficient heads cs ν i) = desired)

/-- The first m labels are ALL original complete inputs in original order;
the last two are actual lowerPart E/F. One lower certificate and one raw
valuation are used throughout. No independence premise is introduced. -/
def LiteralSourceLabels : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k) (ν : Nat → Nat),
  (sourceTerms k Γ C E F).length = (sourceCoefficients E F).length + 2 ∧
  ((sourceTerms k Γ C E F).map (fun T => BalancedSyntax.value Γ C.1 T ν) =
    ((BalancedSyntax.comparisonRow E F).atoms.map (fun a =>
      BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) a.2)) ++
      [BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C E) ν,
       BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C F) ν]) ∧
  sourceValuation k Γ C E F ν (sourceCoefficients E F).length =
    BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C E) ν ∧
  sourceValuation k Γ C E F ν ((sourceCoefficients E F).length + 1) =
    BalancedSyntax.value Γ C.1 (BalancedSyntax.Affine.lowerPart k Γ C F) ν ∧
  (BalancedSyntax.genuineCertificate (k :: Γ) C →
    ∀ T ∈ sourceTerms k Γ C E F, BalancedSyntax.genuineExpression Γ T)

/-- Formula labels stay among the original inputs and two literal lower
parts. Instantiation introduces no fresh raw names. Original pair support
is retained as ambient data; exact guard-support equality is NOT claimed. -/
def OriginalSourceSupport : Prop :=
  (∀ (L : Nat) (heads : Nat → NONote) (cs : List Int) (desired : Int),
    ∀ i ∈ (largeFormula L heads cs desired).variables, i < cs.length + 2) ∧
  (∀ (k : Nat) (Γ : List Nat) (C : BalancedSyntax.Certificate (k :: Γ))
    (E F : BalancedSyntax.Upper k) (desired : Int),
    ∀ i ∈ sourceGuardVariables k Γ C E F desired, i ∈ sourceAmbient k Γ C E F)

/-- The finite semantic large guard is equivalent to the ORIGINAL balanced
threshold on EVERY original atom and the exact source sign, for arbitrary
integer desired. All-cancel descent compares the actual lowerPart E/F terms.
No greatest-key, distinctness, cancellation or independently valued basis
assumption is supplied. This does not assert a raw or recursive compiler. -/
def ExactActualSourceLargeFormula : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
  (desired : Int) (ν : Nat → Nat),
  BalancedSyntax.genuineExpression (k :: Γ) E →
  BalancedSyntax.genuineExpression (k :: Γ) F →
  ((sourceFormula E F desired).eval (sourceValuation k Γ C E F ν) ↔
    (∀ a ∈ (BalancedSyntax.comparisonRow E F).atoms,
      BalancedRow.threshold (BalancedSyntax.comparisonRow E F) ≤
        BalancedRow.input (BalancedSyntax.basisValues k Γ C ν) a.2) ∧
    Int.sign ((BalancedSyntax.value (k :: Γ) C E ν : Int) -
      (BalancedSyntax.value (k :: Γ) C F ν : Int)) = desired)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards.Targets
