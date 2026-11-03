module
public import LogicLineages.OrdinalComparison.CommonHeadLargeGuardsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectedDominanceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineSyntaxDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards
open CommonHeadLargeGuards (Formula conjunction disjunction masks maskCoefficient)

/-- Heads are fixed normal ordinal notations. Input labels, not head codes,
are compared by the existing guard syntax. -/
noncomputable def keyEqualFormula (heads : Nat → NONote) (i j : Nat) : Formula := by
  classical
  exact if heads i = heads j then .eq i j else .falsity

/-- Semantic ordinal order on fixed heads, then ordinary input order within
one head. This is NOT numerical order on an encoding of the heads. -/
noncomputable def keyLessFormula (heads : Nat → NONote) (i j : Nat) : Formula := by
  classical
  exact if (heads i).1.repr < (heads j).1.repr then .truth
    else if heads i = heads j then .lt i j else .falsity

noncomputable def blockCoefficient (heads : Nat → NONote) (cs : List Int)
    (ν : Nat → Nat) (i : Nat) : Int := by
  classical
  exact (cs.zipIdx.map (fun a =>
    if heads a.2 = heads i ∧ ν a.2 = ν i then a.1 else 0)).sum

/-- Each bit describes membership in the complete head-and-input block,
including negative bits for every other original occurrence. -/
noncomputable def maskGuard (heads : Nat → NONote) (m i : Nat)
    (mask : List Bool) : Formula :=
  conjunction ((List.range m).map (fun j =>
    if mask.getD j false then keyEqualFormula heads i j
    else .neg (keyEqualFormula heads i j)))

noncomputable def blockFormula (heads : Nat → NONote) (cs : List Int)
    (i : Nat) (desired : Int) : Formula :=
  disjunction (((masks cs.length).filter
    (fun mask => Int.sign (maskCoefficient cs mask) = desired)).map
      (maskGuard heads cs.length i))

noncomputable def canceledFormula (heads : Nat → NONote) (cs : List Int) : Formula :=
  conjunction ((List.range cs.length).map (fun i => blockFormula heads cs i 0))

/-- Every strictly greater actual key must cancel. This does not select the
greatest ORIGINAL key, which may have zero total coefficient. -/
noncomputable def maximalFormula (heads : Nat → NONote) (cs : List Int)
    (i : Nat) : Formula :=
  conjunction ((List.range cs.length).map (fun j =>
    .disj (.neg (keyLessFormula heads i j)) (blockFormula heads cs j 0)))

/-- Exact sign of the difference of two natural-valued LOWER expressions.
All other integer desired signs are false. -/
def differenceSignFormula (left right : Nat) (desired : Int) : Formula :=
  if desired = -1 then .lt left right
  else if desired = 0 then .eq left right
  else if desired = 1 then .lt right left
  else .falsity

/-- The two final labels stand for the actual lower parts. They are not new
raw variables or independently ranging basis values. -/
noncomputable def signFormula (heads : Nat → NONote) (cs : List Int)
    (desired : Int) : Formula :=
  .disj
    (.conj (canceledFormula heads cs)
      (differenceSignFormula cs.length (cs.length + 1) desired))
    (if desired = 0 then .falsity else
      disjunction ((List.range cs.length).map (fun i =>
        .conj (blockFormula heads cs i desired) (maximalFormula heads cs i))))

/-- Bounds apply to EVERY original atom occurrence, even one whose block
cancels. L will be the threshold of the original signed source row. -/
noncomputable def largeFormula (L : Nat) (heads : Nat → NONote)
    (cs : List Int) (desired : Int) : Formula :=
  .conj (conjunction ((List.range cs.length).map (Formula.bound L)))
    (signFormula heads cs desired)

/-- Literal source order: positive left occurrences, then negative right
occurrences. No canceled occurrence is dropped. -/
def signedAtoms {k : Nat} (E F : BalancedSyntax.Upper k) :
    List (Int × BalancedSyntax.Atom k) :=
  E.atoms.map (fun a => ((a.1 + 1 : Int), a.2)) ++
    F.atoms.map (fun a => (-((a.1 + 1 : Int)), a.2))

def sourceCoefficients {k : Nat} (E F : BalancedSyntax.Upper k) : List Int :=
  (signedAtoms E F).map Prod.fst

def sourceHeads {k : Nat} (E F : BalancedSyntax.Upper k) (i : Nat) : NONote :=
  ((signedAtoms E F).map (fun a => a.2.head)).getD i 0

/-- One preceding-level source term per original complete input, followed by
the literal left and right lower parts, ALL under the shared certificate C.1. -/
noncomputable def sourceTerms (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k) :
    List (BalancedSyntax.Syntax Γ) :=
  (signedAtoms E F).map (fun a => BalancedSyntax.Affine.completeInput k Γ C a.2) ++
    [BalancedSyntax.Affine.lowerPart k Γ C E, BalancedSyntax.Affine.lowerPart k Γ C F]

/-- The default is the literal support-free numeral zero. In-range guard
labels always refer to sourceTerms; this does not extend the raw valuation. -/
noncomputable def sourceTerm (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (i : Nat) : BalancedSyntax.Syntax Γ :=
  (sourceTerms k Γ C E F).getD i (BalancedSyntax.Affine.numeral Γ 0)

noncomputable def sourceValuation (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (ν : Nat → Nat) (i : Nat) : Nat :=
  BalancedSyntax.value Γ C.1 (sourceTerm k Γ C E F i) ν

noncomputable def sourceFormula {k : Nat} (E F : BalancedSyntax.Upper k)
    (desired : Int) : Formula :=
  largeFormula (BalancedRow.threshold (BalancedSyntax.comparisonRow E F))
    (sourceHeads E F) (sourceCoefficients E F) desired

/-- Original pair support remains ambient data, including names that a true
or false large guard happens not to mention after fixed-head simplification. -/
def sourceAmbient (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k) : List Nat :=
  BalancedSyntax.rawVariables (k :: Γ) C E ++ BalancedSyntax.rawVariables (k :: Γ) C F

noncomputable def sourceGuardVariables (k : Nat) (Γ : List Nat)
    (C : BalancedSyntax.Certificate (k :: Γ)) (E F : BalancedSyntax.Upper k)
    (desired : Int) : List Nat :=
  (sourceFormula E F desired).variables.flatMap (fun i =>
    BalancedSyntax.rawVariables Γ C.1 (sourceTerm k Γ C E F i))

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuards
