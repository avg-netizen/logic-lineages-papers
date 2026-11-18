module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDefinitions
public import LogicLineages.OrdinalComparison.WWEncodedClosedPositiveDefinitions
public import LogicLineages.OrdinalComparison.EncodedSuffixKernelDefinitions
public import LogicLineages.PermittedControl.EvaluatorDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluation

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ForwardTranslation

def omegaCode : Nat := rawNoteEncode ClosedPositive.omega.evaluate.1

def leaf (p : List Nat × Nat) : Nat :=
  if p.2 = 1 then encodedNatNote 1 else
  if p.2 = 2 then omegaCode else
  if p.2 % 8 = 3 then encodedNatNote (p.1.getD (p.2 / 8) 0) else 0

noncomputable def branch (f : Nat → Nat) (p : List Nat × Nat × Nat × Nat) : Nat :=
  if p.2.1 = 4 then encodedNaturalSum p.2.2.1 p.2.2.2 else
  if p.2.1 = 5 then encodedNaturalProduct (encodedBaseTwoPower p.2.2.1) p.2.2.2 else
  if p.2.1 = 6 then encodedNatNote (PermittedControl.evaluatorWith f
    (encodedNaturalSum (encodedNaturalProduct omegaCode p.2.2.1) p.2.2.2))
  else 0

noncomputable def evaluate (f : Nat → Nat) (env : List Nat) (code : Nat) : Nat :=
  OrdinalSyntaxComputableFold.indexedFold leaf (branch f) env code

end LogicLineages.ControlSensitivityCurrent.CurrentOrdinalEvaluation
