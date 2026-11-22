module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
open OrdinalComparison FieldComparison
open NaturalAffineGateGraph (Expression)
open OriginalNaturalFieldGates (Interval)
open OriginalPrintedCircuitSequential (Gate Failure)

abbrev RawGate := Nat × Nat × Nat × (Nat × Nat) × Expression
abbrev Args := List Nat × RawGate

def tag (p : Args) : Nat := p.2.1
def source (p : Args) : Nat := p.2.2.1
def payload (p : Args) : Nat × Nat := p.2.2.2.2.1
def expression (p : Args) : Expression := p.2.2.2.2.2

def emptyExpression : Expression := (0,[])

def encodeGate : Gate → RawGate
  | .base (.affine e out) => (0,0,out,(0,0),e)
  | .base (.collapse w) => (1,w.source,w.output,(rawNoteEncode w.head.1,0),emptyExpression)
  | .field (.iterate k s o) => (2,s,o,(k,0),emptyExpression)
  | .field (.entry (.proper lam mu) s o) =>
      (3,s,o,(rawNoteEncode lam.1,rawNoteEncode mu.1),emptyExpression)
  | .field (.count (.proper lam mu) s o) =>
      (4,s,o,(rawNoteEncode lam.1,rawNoteEncode mu.1),emptyExpression)
  | .field (.entry (.identity mu) s o) => (5,s,o,(rawNoteEncode mu.1,0),emptyExpression)
  | .field (.count (.identity mu) s o) => (6,s,o,(rawNoteEncode mu.1,0),emptyExpression)

/-- Values of a finite bank are explicit. The default in getD is never
used by a successful parser, because every read is separately checked. -/
def bank (values : List Nat) (i : Nat) : Nat := values.getD i 0

def inputValue (p : Args) : Nat := bank p.1 (source p)

def parser (p : Args) : Bool :=
  decide (tag p ≤ 6) &&
    (if tag p = 0 then (expression p).2.all (fun term => decide (term.2 < p.1.length))
      else decide (source p < p.1.length))

def identityGuard (p : Nat × Nat) : Bool :=
  terminalScanGuard (p.1,p.1) && decide (rawNormCode p.1 ≤ p.2)

def packBase : Option Nat → Nat
  | none => 1
  | some v => v + 4

def packField : ClosedNaturalFieldResult → Nat
  | none => 2
  | some none => 3
  | some (some v) => v + 4

def packResult : Except Failure Nat → Nat
  | .error .rejectedBase => 1
  | .error .invalidField => 2
  | .error .missedField => 3
  | .ok v => v + 4

def signedBank (p : Args) : Int :=
  (expression p).1 + (expression p).2.foldr
    (fun term acc => term.1 * (bank p.1 term.2 : Int) + acc) 0

def packAffine (z : Int) : Nat := if z.sign = (-1 : Int) then 1 else z.natAbs + 4

def identityValueCode (p : Nat × Nat × Nat) : Nat :=
  if identityGuard (p.1,p.2.1) then p.2.2 + 4 else 2

noncomputable def readCore (f : Nat → Nat) (p : Args) : Nat :=
  if tag p = 0 then packAffine (signedBank p)
  else if tag p = 1 then packBase (ArbitraryFixedHeadCollapse.read f ((payload p).1,inputValue p))
  else if tag p = 2 then packField (closedOrdinaryValueField f (0,(payload p).1,0,0) (inputValue p))
  else if tag p = 3 then packField (closedOrdinaryValueField f (1,0,(payload p).1,(payload p).2) (inputValue p))
  else if tag p = 4 then packField (closedOrdinaryCountField f ((payload p).1,(payload p).2,inputValue p))
  else if tag p = 5 then identityValueCode ((payload p).1,inputValue p,inputValue p)
  else identityValueCode ((payload p).1,inputValue p,0)

noncomputable def readCode (f : Nat → Nat) (p : Args) : Nat :=
  if parser p then readCore f p else 0

def ExactNumericParserAndIdentity : Prop :=
  Primrec parser ∧ Primrec identityGuard ∧
  (∀ (values : List Nat) (g : Gate),
    parser (values,encodeGate g) = true ↔ ∀ n ∈ g.references, n < values.length) ∧
  ∀ (mu : NONote) (x : Nat), identityGuard (rawNoteEncode mu.1,x) = true ↔
    OriginalNaturalFieldGates.IdentityDomain mu x

def ExactNumericGateRead : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (readCode f)) ∧
  (∀ (f : Nat → Nat) (p : Args), readCode f p = 0 ↔ parser p = false) ∧
  ∀ (f : Nat → Nat) (values : List Nat) (g : Gate), (∀ n ∈ g.references, n < values.length) →
    readCode f (values,encodeGate g) = packResult (g.read f (bank values))

def FullOriginalPrintedCircuitNumericRead : Prop :=
  ExactNumericParserAndIdentity ∧ ExactNumericGateRead

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
