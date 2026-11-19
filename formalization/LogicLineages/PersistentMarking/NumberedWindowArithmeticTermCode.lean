import LogicLineages.PersistentMarking.NumberedWindowSyntax
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFields
import LogicLineages.PersistentMarking.NumberedWindowArithmeticHeadCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode
open NumberedWindowSyntax
open NumberedWindowArithmeticPair (pair decode)
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticFields

/- The literal actual NTerm/NArgs AST. Ordered base and extras stay in
separate fields; inferred annotations are not used in place of the
original recorded types and labels. -/
mutual
def encodeTerm : NTerm → Nat
  | .free σ x => encodeNode 0 [encodeTy σ,x]
  | .bound σ i => encodeNode 1 [encodeTy σ,i]
  | .lam σ Q => encodeNode 2 [encodeTy σ,encodeTerm Q]
  | .bottom σ => encodeNode 3 [encodeTy σ]
  | .ordinary f bs => encodeNode 4 [encodeHead f,encodeArgs bs]
  | .numbered f τ k bs es => encodeNode 5 [encodeHead f,encodeTy τ,k,encodeArgs bs,encodeArgs es]
  | .auxApp σ τ Q A => encodeNode 6 [encodeTy σ,encodeTy τ,encodeTerm Q,encodeTerm A]

def encodeArgs : NArgs → Nat
  | .nil => 0
  | .cons Q qs => pair (encodeTerm Q) (encodeArgs qs) + 1
end

/-- Only the original constructor and its exact field arity are
accepted. Recursive term and Args decoding supplies actual subobjects. -/
def assemble (term : Nat → Option NTerm) (args : Nat → Option NArgs) :
    Nat → List Nat → Option NTerm
  | 0, [t,x] => (decodeTy t).map (fun σ => .free σ x)
  | 1, [t,i] => (decodeTy t).map (fun σ => .bound σ i)
  | 2, [t,q] => do
    let σ ← decodeTy t
    let Q ← term q
    pure (.lam σ Q)
  | 3, [t] => (decodeTy t).map NTerm.bottom
  | 4, [g,bs] => do
    let f ← decodeHead g
    let as ← args bs
    pure (.ordinary f as)
  | 5, [g,t,k,bs,es] => do
    let f ← decodeHead g
    let τ ← decodeTy t
    let as ← args bs
    let xs ← args es
    pure (.numbered f τ k as xs)
  | 6, [dom,cod,q,a] => do
    let σ ← decodeTy dom
    let τ ← decodeTy cod
    let Q ← term q
    let A ← term a
    pure (.auxApp σ τ Q A)
  | _, _ => none

mutual
def decodeTermFuel : Nat → Nat → Option NTerm
  | 0, _ => none
  | fuel+1, code => do
    let (tag,fields) ← decodeNode code
    assemble (fun n => decodeTermFuel fuel n) (fun n => decodeArgsFuel fuel n) tag fields

def decodeArgsFuel : Nat → Nat → Option NArgs
  | _, 0 => some .nil
  | 0, _+1 => none
  | fuel+1, code+1 => do
    let (head,tail) ← decode code
    let Q ← decodeTermFuel fuel head
    let qs ← decodeArgsFuel fuel tail
    pure (.cons Q qs)
end

def decodeTerm (code : Nat) : Option NTerm := decodeTermFuel code code

def decodeArgs (code : Nat) : Option NArgs := decodeArgsFuel code code

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode
