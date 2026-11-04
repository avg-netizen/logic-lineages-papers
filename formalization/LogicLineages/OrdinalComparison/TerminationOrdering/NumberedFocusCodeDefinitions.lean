module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeRootPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCodecPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCode
open Source NumberedAuxiliaryCoding NumberedExchangeCode NumberedTypedFocus

abbrev RawValue (Symbol : Type) := List Ty × Ty × Code Symbol
abbrev Frame (Symbol : Type) := Position × Code Symbol
abbrev Trace (Symbol : Type) := RawValue Symbol × List (Frame Symbol)

/-- Reassemble the literal ordered argument entries without changing their types. -/
def entriesCode {Symbol : Type} : List (Ty × Code Symbol) → Code Symbol
  | [] => .argumentsNil
  | (tau, q) :: entries => .argumentsCons tau q (entriesCode entries)

def argumentAt {Symbol : Type} (Gamma : List Ty) (index : Nat) (args : Code Symbol) :
    Option (RawValue Symbol) := do
  let entries ← argumentEntries args
  let selected ← entries[index]?
  pure (Gamma, selected.1, selected.2)

/-- Exactly the five permitted positions; auxiliary application selects only its function. -/
def descendCode {Symbol : Type} : Position → RawValue Symbol → Option (RawValue Symbol)
  | .lam, (Gamma, .arrow domain result, .lam sigma body) =>
    if sigma = domain then some (sigma :: Gamma, result, body) else none
  | .appFunction, (Gamma, tau, .app sigma fn _) =>
    some (Gamma, .arrow sigma tau, fn)
  | .ordinaryBase index, (Gamma, _, .ordinary _ base) => argumentAt Gamma index base
  | .numberedBase index, (Gamma, _, .numbered _ _ _ base _ _) => argumentAt Gamma index base
  | .numberedExtras index, (Gamma, _, .numbered _ _ _ _ _ extras) => argumentAt Gamma index extras
  | _, _ => none

/-- Frames are ordered from the discovered hole outward. Each retains its original root. -/
def traceCode {Symbol : Type} : List Position → RawValue Symbol → Option (Trace Symbol)
  | [], value => some (value, [])
  | position :: path, value => do
    let child ← descendCode position value
    let result ← traceCode path child
    pure (result.1, result.2 ++ [(position, value.2.2)])

def focusCode {Symbol : Type} (path : List Position) (Gamma : List Ty) (tau : Ty)
    (code : Code Symbol) : Option (RawValue Symbol) :=
  (traceCode path (Gamma, tau, code)).map Prod.fst

/-- Replace one existing argument, retaining its type and every other entry. -/
def replaceArgumentCode {Symbol : Type} (index : Nat) (args replacement : Code Symbol) :
    Option (Code Symbol) := do
  let entries ← argumentEntries args
  let selected ← entries[index]?
  pure (entriesCode (entries.set index (selected.1, replacement)))

def wrapCode {Symbol : Type} (frame : Frame Symbol) (replacement : Code Symbol) :
    Option (Code Symbol) :=
  match frame with
  | (.lam, .lam sigma _) => some (.lam sigma replacement)
  | (.appFunction, .app sigma _ arg) => some (.app sigma replacement arg)
  | (.ordinaryBase index, .ordinary head base) =>
    (replaceArgumentCode index base replacement).map (Code.ordinary head)
  | (.numberedBase index, .numbered label head tau base types extras) =>
    (replaceArgumentCode index base replacement).map
      (fun target => .numbered label head tau target types extras)
  | (.numberedExtras index, .numbered label head tau base types extras) =>
    (replaceArgumentCode index extras replacement).map
      (fun target => .numbered label head tau base types target)
  | _ => none

def unwindCode {Symbol : Type} (frames : List (Frame Symbol)) (replacement : Code Symbol) :
    Option (Code Symbol) :=
  frames.foldl (fun current frame => current.bind (fun value => wrapCode frame value))
    (some replacement)

def replaceCode {Symbol : Type} (path : List Position) (Gamma : List Ty) (tau : Ty)
    (code replacement : Code Symbol) : Option (Code Symbol) :=
  (traceCode path (Gamma, tau, code)).bind (fun result => unwindCode result.2 replacement)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCode
