module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealRegularCodeDefinitions
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCoverDefinitions
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular RankedIdealRegularEnumeration

/-- Choice-free enumeration of the actual Boolean-mask/matrix profile states.
Duplicate codes and inactive entries remain present; no quotient enumeration. -/
def profileStates (N : Nat) : List (FiniteProfile.State N) :=
  sets (pairs (functions (fun _ : Fin N => RankedIdealRegularCode.bools))
    (functions (fun _ : Fin N => functions (fun _ : Fin N => RankedIdealRegularCode.bools))))

theorem profileStatesComplete (N : Nat) (S : FiniteProfile.State N) : S ∈ profileStates N := by
  apply (StatementChecks.setsExact _ S).mpr
  intro C _
  apply StatementChecks.pairsComplete
  · exact StatementChecks.functionsComplete N _ C.1
      (fun i => RankedIdealRegularCode.bools_complete (C.1 i))
  · apply StatementChecks.functionsComplete N
    intro i
    exact StatementChecks.functionsComplete N _ (C.2 i)
      (fun j => RankedIdealRegularCode.bools_complete (C.2 i j))

/-- Literal source-family compiler, including P4/C4 and empty forbidden graphs.
The finite presentation is assembled by actual list algorithms, not choice. -/
def sourceCode (F : List RawGraph) : RankedIdealRegularCode.Code where
  machine := sourceMachine F
  stateDecidableEq := inferInstanceAs
    (DecidableEq (FiniteProfile.State (familyBound (pathInput :: cycleInput :: F))))
  states := profileStates (familyBound (pathInput :: cycleInput :: F))
  complete := profileStatesComplete (familyBound (pathInput :: cycleInput :: F))

def sourceCover (F : List RawGraph) : List RankedIdealRegularCode.Code :=
  RankedIdealCover.cover (sourceCode F)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealSourceCode
