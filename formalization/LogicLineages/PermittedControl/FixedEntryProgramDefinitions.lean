module
public import LogicLineages.PermittedControl.OrdinalEndpointCodeDefinitions
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

/-- Literal raw code for a finite ordinal. -/
def finiteOrdinalCode (n : Nat) : Nat := if n=0 then 0 else ordinalNodeCode 0 (n-1) 0

/-- Source canonical initial state, computed by actual ordinary ordinal addition. -/
def canonicalInitialCode (lambda t : Nat) : Nat :=
  ordinalAddCode lambda (finiteOrdinalCode (t-rawNormCode lambda))

/-- The actual partial fixed entry map, with input (lambda,mu,t). Skipped targets
remain partial; no artificial result is assigned on small inputs. -/
def fixedEntryProgram (f : Nat → Nat) (p : Nat×Nat×Nat) : Part (Nat×Nat) :=
  entryPartialWith f (canonicalInitialCode p.1 p.2.2,p.2.1)

end LogicLineages.PermittedControl
