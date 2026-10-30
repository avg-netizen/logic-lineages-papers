module

public import LogicLineages.ModelsAlgebra.Forests.AgeApplicationDefinitions

/-! Exact source application and empty-class convention after paper03 prop:age.
No positivity algorithm for arbitrary forbidden families is claimed. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Targets

open AgeConstruction

def RealizedForestAgeNonempty : Prop :=
  ∀ K A, HasForestAge K A → ClassNonempty K

def AvoidanceClassHereditary : Prop :=
  ∀ U, ClassHereditary (AvoidanceClass U)

def AvoidanceClassNonemptyCriterion : Prop :=
  ∀ U, ClassNonempty (AvoidanceClass U) ↔ ∀ B ∈ U, Nonempty B.Carrier

def NoEmptyCodeTestCorrect : Prop :=
  ∀ (U : List FiniteCode.Code) (hU : FiniteCode.FamilyValid U),
    noEmptyTest U = true ↔ ClassNonempty (AvoidanceClass (FiniteCode.toFamily U hU))

def NoEmptyCodeTestPrimitiveRecursive : Prop := Primrec noEmptyTest

def ForbiddenForestAgeCriterion : Prop :=
  ∀ U, (∃ A : CountableOrderForest, HasForestAge (AvoidanceClass U) A) ↔
    CertificateSearch.HasJEP U ∧ ∀ B ∈ U, Nonempty B.Carrier

end LogicLineages.ModelsAlgebra.Forests.Targets
