module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedClassCandidatesPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodePrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSyntaxBoundsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimary
open Source NumberedAuxiliaryCoding NumberedAuxiliaryEnumeration NumberedUniformPackedDecoding

abbrev Window (n : Nat) := List (Fin n) × List Ty

/-- The ORIGINAL enumeration, with its actual size/label/context bounds.
Only its representation has changed from dependent typed terms to their
already accepted raw structural codes. -/
def classCodes {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) : List (RawPacked n) :=
  let bounds := NumberedSyntaxBoundsPrimrec.codeBounds q.2
  (enumerate S (sourceHeads arity symbols S) bounds.2 bounds.1 Gamma.length (2*bounds.1)).map
    (fun c => (q.1,c))

def candidates {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) : List (RawPacked n) :=
  (classCodes arity symbols S Gamma q).filterMap (rawStructuralDecode arity Gamma)

def vertices {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) : List (RawPacked n) := q :: candidates arity symbols S Gamma q

def step {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (pool reached : List (RawPacked n)) : List (RawPacked n) :=
  reached ++ pool.filter (fun r => reached.any
    (fun a => NumberedExchangeCode.packedCodeExchange arity symbols S a r))

def reachable {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) (fuel : Nat) : List (RawPacked n) :=
  (step arity symbols S (vertices arity symbols S Gamma q))^[fuel] [q]

def primaryList {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) : List (RawPacked n) :=
  reachable arity symbols S Gamma q (vertices arity symbols S Gamma q).length

def primaryTest {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : RawPacked n) : Bool := decide (r ∈ primaryList arity symbols S Gamma q)

def packedNumber {n : Nat} (q : RawPacked n) : Nat :=
  Nat.pair (NumberedLeastCodeRepresentative.typeNumber q.1)
    (NumberedLeastCodeRepresentative.codeNumber q.2)

def classNumberTest {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) (value : Nat) : Bool :=
  (rawPackedDecode n arity Gamma value).any (primaryTest arity symbols S Gamma q)

def representative {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q : RawPacked n) : Nat :=
  (List.range (packedNumber q + 1)).findIdx (classNumberTest arity symbols S Gamma q)

def canonicalCarrier (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat) : Bool :=
  (rawUniverseDecode n arity symbols S Gamma value).any
    (fun q => decide (representative arity symbols S Gamma q = value))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ContextUniformPrimary
