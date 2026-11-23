module

public import LogicLineages.NativeModule.PersistentMarking.Syntax
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticPair

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCode
open NumberedWindowArithmeticPair (pair decode)

/-- Literal ground and arrow type codes. Arrow fields really are the
encoded original domain and codomain, in order. -/
def encodeTy : Ty → Nat
  | .ground => 0
  | .arrow σ τ => pair (encodeTy σ) (encodeTy τ) + 1

def decodeTyFuel : Nat → Nat → Option Ty
  | _, 0 => some .ground
  | 0, _+1 => none
  | fuel+1, code+1 => do
    let (dom,cod) ← decode code
    let σ ← decodeTyFuel fuel dom
    let τ ← decodeTyFuel fuel cod
    pure (.arrow σ τ)

def decodeTy (code : Nat) : Option Ty := decodeTyFuel code code

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTyCode
