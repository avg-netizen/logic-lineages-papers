import LogicLineages.PersistentMarking.NumberedWindowPrimaryClassListChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowSimulationData

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClass
open NumberedWindowSyntax NumberedWindowPrimaryClassList NumberedWindowArithmeticTermCode

abbrev finiteC (Γ : List Ty) : Spine.BoundContext :=
  Spine.BoundContext.«prefix» Γ Spine.EmptyContext

/-- Least actual literal Nat code over the already exact finite list of
the original Primary class. Duplicate representatives do not change
the least code. Neither the class nor the code is obtained by choice. -/
def leastCode (S : Spine.Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (Q : NTerm) : Option Nat :=
  ((finiteClassList S K Γ τ Q).map encodeTerm).min?

/-- Decode the same computed least Nat code with the exact original raw
term parser; typing and actual class membership are proved separately. -/
def representative (S : Spine.Signature) (K : List Ty) (Γ : List Ty) (τ : Ty)
    (Q : NTerm) : Option NTerm :=
  (leastCode S K Γ τ Q).bind decodeTerm

end LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClass
