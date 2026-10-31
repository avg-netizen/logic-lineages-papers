module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerLabelEqualityProof
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityProof
open Turing PredictionCompilerTapeSupport PredictionCompilerLabelEquality PredictionCompilerAlphabetEquality
open PredictionCompilerPostEquality PredictionCompilerPostEqualityTargets

private theorem direction_iff (d e : Dir) : directionEq d e = true ↔ d = e := by
  cases d <;> cases e <;> simp [directionEq]

private theorem work_input_iff (f g : TapeAlphabet → Store → TapeAlphabet) :
    sameInputs workEq f g = true ↔ f = g :=
  PredictionCompilerAlphabetEqualityProof.exactInputFunctionComparison _ workEq
    PredictionCompilerAlphabetEqualityProof.exactWorkSymbolComparison f g

private theorem store_input_iff (f g : TapeAlphabet → Store → Store) :
    sameInputs (fun a b : Store => decide (a = b)) f g = true ↔ f = g :=
  PredictionCompilerAlphabetEqualityProof.exactInputFunctionComparison _ _ (by simp) f g

private theorem bool_input_iff (f g : TapeAlphabet → Store → Bool) :
    sameInputs (fun a b : Bool => decide (a = b)) f g = true ↔ f = g :=
  PredictionCompilerAlphabetEqualityProof.exactInputFunctionComparison _ _ (by simp) f g

private theorem label_input_iff (f g : TapeAlphabet → Store → TapeLabel) :
    sameInputs labelEq f g = true ↔ f = g :=
  PredictionCompilerAlphabetEqualityProof.exactInputFunctionComparison _ labelEq
    PredictionCompilerLabelEqualityProof.exactTapeLabelComparison f g

theorem exactTapeStatementEquality : ExactTapeStatementEquality := by
  intro q
  induction q <;> intro r <;> cases r <;>
    simp_all [tapeEq, direction_iff, work_input_iff, store_input_iff, bool_input_iff,
      label_input_iff, and_assoc]

private theorem optional_iff (q r : Option TapeStatement) :
    optionalTapeEq q r = true ↔ q = r := by
  cases q <;> cases r <;> simp [optionalTapeEq, show ∀ q r, tapeEq q r = true ↔ q = r from exactTapeStatementEquality]

theorem exactPostLabelEquality : ExactPostLabelEquality := by
  rintro ⟨q, s⟩ ⟨r, t⟩
  simp only [postEq, Bool.and_eq_true, optional_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨rfl, rfl⟩
    rfl
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The actual compiled labels now have a decision procedure built from
finite Boolean tests, with no Classical.decEq in the algorithm. -/
def postDecidableEq : DecidableEq PostLabel := fun a b =>
  decidable_of_iff (postEq a b = true) (exactPostLabelEquality a b)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerPostEqualityProof
