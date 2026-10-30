module

public import LogicLineages.ModelsAlgebra.Differential.SpectralResultantCodeDefinitions
public import LogicLineages.ModelsAlgebra.Differential.BoundedPolynomialDivisionDefinitions
public import LogicLineages.ModelsAlgebra.Differential.SpectralConstraintDefinitions
public import LogicLineages.ModelsAlgebra.Differential.PolynomialCertificateSearchDefinitions
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

/-! The source spectral algorithm takes rational polynomial codes only. Its
promise is literal monicity, positive order, rationally independent full roots
in the actual splitting field and a nonzero lower-order q. Roots occur only in
that mathematical promise, never in the program's input or search. -/
namespace LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm

universe u

abbrev Input := DensePolynomial.Code × ℕ × DensePolynomial.Code

def order (t : Input) : ℕ := PolynomialCertificateSearch.degree t.1
def sourceBase (n : ℕ) : ℕ := 2 * n + 2

noncomputable def equation (t : Input) : Polynomial ℚ := DensePolynomial.value t.1
noncomputable def lowerPolynomial (t : Input) : MvPolynomial (Fin (equation t).natDegree) ℚ :=
  BoxPolynomialCode.value (equation t).natDegree t.2.1 t.2.2

def SourcePromise (t : Input) : Prop :=
  2 ≤ t.2.1 ∧ lowerPolynomial t ≠ 0 ∧ (equation t).Monic ∧ 0 < (equation t).natDegree ∧
  ∃ root : Fin (equation t).natDegree → (equation t).SplittingField,
    LinearIndependent ℚ root ∧
    (equation t).map (algebraMap ℚ (equation t).SplittingField) =
      ∏ i : Fin (equation t).natDegree, (Polynomial.X - Polynomial.C (root i))

def InputConstrained (t : Input) : Prop := ConstrainedLinear.{u} (equation t) (lowerPolynomial t)

def prepare (t : Input) : BoundedPolynomialDivision.Input :=
  let n := order t
  let C := sourceBase n
  let B := max C t.2.1
  (n, B,
    BoxPolynomialCode.rebase n C B (SpectralResultantCode.obstruction n C t.1),
    BoxPolynomialCode.rebase n t.2.1 B t.2.2)

def search (t : Input) : Part Bool := BoundedPolynomialDivision.search (prepare t)

end LogicLineages.ModelsAlgebra.Differential.SpectralAlgorithm
