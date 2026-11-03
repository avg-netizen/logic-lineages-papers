module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Targets
open BalancedSyntax BalancedEvaluation

/-- Exact original payload, signed occurrence metadata and EACH printed
threshold component. All actual normal heads, offsets, positive factors,
outside coefficients and duplicate occurrences are unrestricted. -/
def ExactOriginalMetadata : Prop := ∀ (k : Nat) (Γ : List Nat) (E F : Upper k),
  let e := encodeSyntax (k::Γ) E
  let f := encodeSyntax (k::Γ) F
  let row := comparisonRow E F
  upperAtoms e f = (E.atoms++F.atoms).map encodeAtom ∧
  coefficients e f = BalancedLargeGuards.sourceCoefficients E F ∧
  headCodes e f = BalancedLargeGuardsCode.encodeHeads
    ((BalancedLargeGuards.signedAtoms E F).map (fun a => a.2.head)) ∧
  originalConstant e f = row.constant ∧
  outsideCoefficients k e f = row.remainder ∧
  coefficientMass e f = BalancedRow.coefficientMass row ∧
  outsideMaximum k e f = BalancedRow.outsideMaximum row ∧
  multiplierMaximum k e f = BalancedRow.multiplierMaximum row ∧
  offsetMaximum e f = BalancedRow.offsetMaximum row ∧
  normMaximum e f = BalancedRow.normMaximum row ∧
  threshold k e f = BalancedRow.threshold row

/-- The actual lower certificate C.1 and the literal ordered source terms,
not a new family of independently valued labels. Equality is at source-code
level, retains the final two lower parts, and holds even when Γ is empty. -/
def ExactLiteralSourceLabels : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k::Γ)) (E F : Upper k),
  lowerCertificate (encodeCertificate (k::Γ) C) = encodeCertificate Γ C.1 ∧
  termCodes k Γ (encodeCertificate (k::Γ) C)
      (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) =
    (BalancedLargeGuards.sourceTerms k Γ C E F).map (encodeSyntax Γ)

/-- Exact existing postfix code for the source formula, and exact assembly
with the same encoded lower certificate and ordered literal source terms.
No genuine-head premise, runtime oracle or recursive compiler is introduced. -/
def ExactAssembledSourceCode : Prop := ∀ (k : Nat) (Γ : List Nat)
  (C : Certificate (k::Γ)) (E F : Upper k) (desired : Int),
  formulaCode k (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) desired =
    CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired) ∧
  assemble k Γ (encodeCertificate (k::Γ) C)
      (encodeSyntax (k::Γ) E) (encodeSyntax (k::Γ) F) desired =
    (encodeCertificate Γ C.1,
      (BalancedLargeGuards.sourceTerms k Γ C E F).map (encodeSyntax Γ),
      CommonHeadCompiler.encode (BalancedLargeGuards.sourceFormula E F desired))

/-- Genuine uniform primitive recursion for every numeric adapter map on
arbitrary finite raw inputs. Malformed codes use the accepted decode defaults;
they are not asserted to encode valid source syntax or normal heads. -/
def UniformPrimitiveRecursive : Prop :=
  Primrec₂ upperAtoms ∧
  Primrec₂ coefficients ∧
  Primrec₂ headCodes ∧
  Primrec₂ originalConstant ∧
  Primrec (fun p : Nat × Nat × Nat => outsideCoefficients p.1 p.2.1 p.2.2) ∧
  Primrec₂ factors ∧
  Primrec normOffset ∧
  Primrec₂ coefficientMass ∧
  Primrec (fun p : Nat × Nat × Nat => outsideMaximum p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat => multiplierMaximum p.1 p.2.1 p.2.2) ∧
  Primrec₂ offsetMaximum ∧
  Primrec₂ normMaximum ∧
  Primrec (fun p : Nat × Nat × Nat => threshold p.1 p.2.1 p.2.2) ∧
  Primrec lowerCertificate ∧
  Primrec (fun p : Nat × List Nat × Nat × Nat × Nat =>
    termCodes p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Int => formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
    assemble p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapter.Targets
