module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowPositivePathAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddress
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowFieldAlgorithm (pack packNode unpackNode)
open NumberedWindowPositivePathAlgorithm (edgeView)
open NumberedWindowScalarAlgorithm (Settings least)

def functionField (n : Nat) : Option Nat :=
  match unpackNode n with
  | some (6,[_,_,function,_]) => some function
  | _ => none

def functionChild (n : Nat) : Option Nat :=
  match unpackNode n with
  | some (5,[child]) => some child
  | _ => none

/-- Read both function fields and the actual auxFunction child of the
supplied direct application certificate. Recompute the target's least
code at the original function type and in the unchanged context. -/
def functionWitness (s : Settings) (source certificate : Nat) : Option (Nat × Nat) := do
  let (context,ty,_) ← addressView source
  let (Q,w,R) ← edgeView certificate
  let previous ← functionField Q
  let next ← functionField R
  let child ← functionChild w
  let canonical ← least s context ty next
  pure (packNode 3 [pack context,ty,canonical],packNode 1 [previous,next,child])

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddress
