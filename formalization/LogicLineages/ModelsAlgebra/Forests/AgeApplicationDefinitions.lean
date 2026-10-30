module

public import LogicLineages.ModelsAlgebra.Forests.AgeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.CertificateSearchDefinitions

/-! Actual forbidden-class age applications and the finite empty-carrier input
check. The Boolean below is interpreted on validated finite codes; it is not a
JEP test and does not replace validation or Carter's missing algorithm. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeConstruction

def AvoidanceClass (U : List FiniteOrderForest) (F : FiniteOrderForest) : Prop :=
  AvoidsForbidden U F.Carrier

def NoEmptyCode (U : List FiniteCode.Code) : Prop := ∀ c ∈ U, 0 < c.1

instance noEmptyCodeDecidable (U : List FiniteCode.Code) : Decidable (NoEmptyCode U) := by
  unfold NoEmptyCode
  infer_instance

def noEmptyTest (U : List FiniteCode.Code) : Bool := decide (NoEmptyCode U)

end LogicLineages.ModelsAlgebra.Forests.AgeConstruction
