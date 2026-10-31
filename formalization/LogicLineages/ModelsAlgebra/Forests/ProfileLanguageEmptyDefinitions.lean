module
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularDefinitions
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Card

/-! Finite saturation for the actual ranked machine. A DecidableEq instance
is explicit in generic saturation and computationally available for the
profile machine's Boolean-code state space. No state enumeration via classical
choice or Carter graph/tree relation is used. -/
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty
open RankedParse ProfileAutomatonEncoding ProfileSourceRegular

def termHeight : Term → Nat
  | .atom => 1
  | .node _ l r => 1 + max (termHeight l) (termHeight r)

def operations : Finset Operation := {.union, .join}

def reachStep (M : Machine) [DecidableEq M.State] (S : Finset M.State) : Finset M.State :=
  S ∪ {M.leaf} ∪ operations.biUnion
    (fun o => S.biUnion (fun x => S.image (M.node o x)))

def reachable (M : Machine) [DecidableEq M.State] : Nat → Finset M.State
  | 0 => ∅
  | n + 1 => reachStep M (reachable M n)

def acceptingStates (M : Machine) [DecidableEq M.State] : Finset M.State :=
  Finset.univ.filter (fun q => M.accept q = true)

def languageEmpty (M : Machine) [DecidableEq M.State] : Bool :=
  decide (reachable M (Fintype.card M.State) ∩ acceptingStates M = ∅)

def sourceLanguageEmpty (F : List RawGraph) : Bool :=
  letI : DecidableEq (sourceMachine F).State := by
    change DecidableEq (FiniteProfile.State (familyBound (pathInput :: cycleInput :: F)))
    infer_instance
  languageEmpty (sourceMachine F)

end LogicLineages.ModelsAlgebra.Forests.ProfileLanguageEmpty
