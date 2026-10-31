module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompilerStatementChecks
public import Mathlib.Data.Finset.Sort
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision
open FirstOrder Language

/-- Compile using a supplied explicit finite encoding, without choosing one. -/
def satisfiableEncoded {Q : Type} {n : Nat} (e : Q ≃ Fin n)
    (p : presburger.Formula Q) : Bool :=
  CotreePresburgerCompiler.satisfiable (p.relabel e)

/-- Ordered finite enumeration is executable, as in the existing formula
constructor's `existsOf`; this is not the choice-based `Fintype.equivFin`. -/
def satisfiable {Q : Type} [Fintype Q] [LinearOrder Q] (p : presburger.Formula Q) : Bool :=
  satisfiableEncoded (Fintype.orderIsoFinOfCardEq Q rfl).toEquiv.symm p
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecision
