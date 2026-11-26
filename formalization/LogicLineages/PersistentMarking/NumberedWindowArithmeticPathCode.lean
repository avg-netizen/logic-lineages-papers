import LogicLineages.PersistentMarking.NumberedWindowClassPathWitnessBits
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticRawWitnessCode
open NumberedWindowPathWitnessBits NumberedWindowClassPathWitnessBits

/-- Literal ordered hop data. Endpoints external to the supplied list
are not synthesized by the codec. -/
def encodeRawHop (e : RawHop) : Nat :=
  encodeNode 0 [encodeTerm e.target,encodeWitness e.witness]

def assembleRawHop : Nat → List Nat → Option RawHop
  | 0, [t,w] => do
    let target ← decodeTerm t
    let witness ← decodeWitness w
    pure ⟨target,witness⟩
  | _, _ => none

def decodeRawHop (code : Nat) : Option RawHop :=
  (decodeNode code).bind (fun p => assembleRawHop p.1 p.2)

/-- Preserve both original possible raw class representatives. -/
def encodeClassEdge (e : ClassEdgeWitness) : Nat :=
  encodeNode 1 [encodeTerm e.source,encodeTerm e.target,encodeWitness e.witness]

def assembleClassEdge : Nat → List Nat → Option ClassEdgeWitness
  | 1, [q,r,w] => do
    let source ← decodeTerm q
    let target ← decodeTerm r
    let witness ← decodeWitness w
    pure ⟨source,target,witness⟩
  | _, _ => none

def decodeClassEdge (code : Nat) : Option ClassEdgeWitness :=
  (decodeNode code).bind (fun p => assembleClassEdge p.1 p.2)

/-- Keep the actual supplied target class code, not a recomputed or
assumed equal normalization. The semantic checker pays this separately. -/
def encodeClassHop (e : ClassHop) : Nat :=
  encodeNode 2 [e.targetCode,encodeClassEdge e.edge]

def assembleClassHop : Nat → List Nat → Option ClassHop
  | 2, [target,edge] => (decodeClassEdge edge).map (ClassHop.mk target)
  | _, _ => none

def decodeClassHop (code : Nat) : Option ClassHop :=
  (decodeNode code).bind (fun p => assembleClassHop p.1 p.2)

def encodeRawPath (es : List RawHop) : Nat := encodeListOf encodeRawHop es
def decodeRawPath (code : Nat) : Option (List RawHop) := decodeListOf decodeRawHop code

def encodeClassPath (es : List ClassHop) : Nat := encodeListOf encodeClassHop es
def decodeClassPath (code : Nat) : Option (List ClassHop) := decodeListOf decodeClassHop code

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCode
