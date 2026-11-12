module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedExpansion NumberedMultisetNumeric NumberedLeastCodeRepresentative
/-- All numerical role/type annotations are permitted; only original raw Code
and context encoding are needed for the exact unchanged expansion list. -/
def NativeExpansion : Prop := ∀ (n c role typ : Nat)
    (s : OriginalHereditaryWorkBound.State (Fin n)),
  evaluate expansion (List.Vector.ofFn ![jobNumber role typ (OriginalHereditaryExpansion.jobNumber c s)]) =
    numbersNumber (values role typ (codeNumber s.code)
      ((OriginalHereditaryWorkBound.successors s).map (OriginalHereditaryExpansion.jobNumber c)))
def Forgetting : Prop := ∀ role typ raw (jobs : List Nat),
  (values role typ raw jobs).map forgetNumber = jobs
/-- Every individual decorated job forgets to the exact original raw job, on
all numeric vectors; no role validity or source premise is smuggled in. -/
def DecorateForgetting : Prop := ∀ k role typ raw job : Nat,
  evaluate forget (List.Vector.ofFn ![evaluate decorate
    (List.Vector.ofFn ![k,role,typ,raw,job])]) = job

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTargets
