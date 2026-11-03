module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedLargeGuardsCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter
open BalancedEvaluation

/-- All ORIGINAL atom payloads, left first and right second. Stored outer
coefficients, head codes, offsets and complete factor lists are kept verbatim,
including duplicate occurrences. No sorting or collection takes place. -/
def upperAtoms (E F : Nat) : List AtomData :=
  (upperData E).2.2 ++ (upperData F).2.2

/-- The stored natural q denotes q+1, on both sides of the comparison. -/
def coefficients (E F : Nat) : List Int :=
  ((upperData E).2.2.map (fun a => (a.1+1 : Int))) ++
    ((upperData F).2.2.map (fun a => -((a.1+1 : Int))))

def headCodes (E F : Nat) : List Nat :=
  (upperAtoms E F).map (fun a => a.2.1)

def originalConstant (E F : Nat) : Int :=
  ((upperData E).1 : Int) - ((upperData F).1 : Int)

/-- Exactly k signed outside coefficients. Missing raw entries are zero;
excess raw entries are ignored, as in the accepted numeric source interface. -/
def outsideCoefficients (k E F : Nat) : List Int :=
  (List.range k).map (fun j =>
    ((upperData E).2.1.getD j 0 : Int) - ((upperData F).2.1.getD j 0 : Int))

/-- EVERY common-basis position is positive, including a missing raw entry.
The original stored factor list remains unchanged in upperAtoms. -/
def factors (k : Nat) (a : AtomData) : List Nat :=
  (List.range k).map (fun j => a.2.2.2.getD j 0+1)

noncomputable def normOffset (a : AtomData) : Nat :=
  rawNormCode a.2.1+a.2.2.1

def coefficientMass (E F : Nat) : Nat :=
  ((coefficients E F).map Int.natAbs).sum

def outsideMaximum (k E F : Nat) : Nat :=
  BalancedRow.maximum ((outsideCoefficients k E F).map Int.natAbs)

def multiplierMaximum (k E F : Nat) : Nat :=
  max 1 (BalancedRow.maximum ((upperAtoms E F).flatMap (factors k)))

noncomputable def offsetMaximum (E F : Nat) : Nat :=
  BalancedRow.maximum ((upperAtoms E F).map normOffset)

noncomputable def normMaximum (E F : Nat) : Nat :=
  BalancedRow.maximum ((headCodes E F).map rawNormCode)

/-- The printed balanced threshold of the ENTIRE original signed row. All
five budgets and K are computed before any head/input block cancellation. -/
noncomputable def threshold (k E F : Nat) : Nat :=
  BalancedNumerical.threshold (originalConstant E F)
    (coefficientMass E F) (outsideMaximum k E F) (multiplierMaximum k E F)
    (offsetMaximum E F) (normMaximum E F)

/-- Descend through the given certificate, not a reconstructed basis. -/
def lowerCertificate (C : Nat) : Nat := (certificateData C).1

/-- One literal complete input per original occurrence, then the left and
right outside terms. The SAME C is passed to every accepted affine constructor.
The outer sign has no role in the complete-input expression. -/
noncomputable def termCodes (k : Nat) (Γ : List Nat) (C E F : Nat) : List Nat :=
  (upperAtoms E F).map (fun a =>
    BalancedAffineCode.completeInput k Γ C (Encodable.encode a)) ++
    [BalancedAffineCode.lowerPart k Γ C E, BalancedAffineCode.lowerPart k Γ C F]

noncomputable def formulaCode (k E F : Nat) (desired : Int) : BalancedLargeGuardsCode.Code :=
  BalancedLargeGuardsCode.largeCode (threshold k E F) (headCodes E F)
    (coefficients E F) desired

abbrev Result := Nat × List Nat × BalancedLargeGuardsCode.Code

/-- A single-level payload, with its lower shape Γ still explicit in the
input. The caller retains the original pair's ambient support; this adapter
does not infer support from surviving blocks or simplified guard instructions. -/
noncomputable def assemble (k : Nat) (Γ : List Nat) (C E F : Nat)
    (desired : Int) : Result :=
  (lowerCertificate C, termCodes k Γ C E F, formulaCode k E F desired)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter
