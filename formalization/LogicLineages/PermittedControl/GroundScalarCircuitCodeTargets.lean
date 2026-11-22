module
public import LogicLineages.PermittedControl.GroundScalarCircuitTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontendTargets

@[expose] public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarCode)
open OriginalPrintedCircuitSequential (Gate Topological)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate emptyExpression)
open NaturalAffineGateGraph (Expression)
open PreparedProjection (PlainPreparedFormula)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open OriginalPrintedRawFamilyFrontend (Args encodeInput)
open SelectedGeneratedSource (scalarValueWith)

/-- Move node names (odd) up by `k` nodes; input names (even) are fixed. -/
def renameName (k m : Nat) : Nat := if m % 2 = 1 then m + 2 * k else m

def renameGate (k : Nat) (g : RawGate) : RawGate :=
  (g.1,renameName k g.2.1,renameName k g.2.2.1,g.2.2.2.1,
    (g.2.2.2.2.1,g.2.2.2.2.2.map (fun t => (t.1,renameName k t.2))))

def leafGate (e : Expression) : RawGate := (0,0,nodeName 0,(0,0),e)

def addGate (la lb : Nat) : RawGate :=
  (0,0,nodeName (la+lb),(0,0),(0,[(1,nodeName (la-1)),(1,nodeName (la+lb-1))]))

def shiftGate (head la : Nat) : RawGate := (1,nodeName (la-1),nodeName la,(head,0),emptyExpression)

/-- The circuit of a scalar code, with node counter starting at zero, by
recursion on the accepted `scalarCode` (tag `n % 4`). -/
def relCode (n : Nat) : List RawGate :=
  if h0 : n % 4 = 0 then [leafGate (1,[])]
  else if h1 : n % 4 = 1 then [leafGate (1,[(1,inputName (n / 4))])]
  else
    have hn : 0 < n := by omega
    have hd : n / 4 < n := Nat.div_lt_self hn (by decide)
    have hl : (n / 4).unpair.1 < n := (Nat.unpair_left_le _).trans_lt hd
    have hr : (n / 4).unpair.2 < n := (Nat.unpair_right_le _).trans_lt hd
    if n % 4 = 2 then
      relCode (n / 4).unpair.1 ++ (relCode (n / 4).unpair.2).map (renameGate (relCode (n / 4).unpair.1).length) ++
        [addGate (relCode (n / 4).unpair.1).length (relCode (n / 4).unpair.2).length]
    else relCode (n / 4).unpair.2 ++ [shiftGate (n / 4).unpair.1 (relCode (n / 4).unpair.2).length]
termination_by n

def strictRowCode (lo hi : Nat) : Nat :=
  6 * Encodable.encode (((0 : Nat),(0 : Nat),((-1 : Int),
    [((1 : Int),((0 : Nat),hi,(0 : Int),(0 : Int))),((-1 : Int),((0 : Nat),lo,(0 : Int),(0 : Int)))])) :
      NormalForm.Code.AtomData) + 2

def weakRowCode (lo hi : Nat) : Nat :=
  6 * Encodable.encode (((0 : Nat),(0 : Nat),((0 : Int),
    [((1 : Int),((0 : Nat),hi,(0 : Int),(0 : Int))),((-1 : Int),((0 : Nat),lo,(0 : Int),(0 : Int)))])) :
      NormalForm.Code.AtomData) + 2

/-- Code of `counterFormula`. -/
def counterCode (tag a b : Nat) : Nat :=
  if tag = 0 then strictRowCode b a
  else if tag = 1 then weakRowCode b a
  else 6 * Nat.pair (strictRowCode a b) (strictRowCode b a) + 5

/-- Raw compiler from a relation tag and two normalised scalar codes to the
closed-block query arguments (Opus A's interface). -/
def queryCode (tag a b : Nat) : Args :=
  (((List.range (a + b + 1)).map inputName,
    counterCode tag (nodeName ((relCode a).length - 1))
      (nodeName ((relCode a).length + (relCode b).length - 1)),
    relCode a ++ (relCode b).map (renameGate (relCode a).length)),true)

/-- Literal calibration of the code circuit against the typed compiler at any counter. -/
def CircuitCalibration : Prop :=
  ∀ {ι : Type} (index : ι → Nat) (s : Scalar ι) (k : Nat),
    (circuitOf index s k).1.map encodeGate = (relCode (scalarCode index s)).map (renameGate k) ∧
    (circuitOf index s k).2.2 = k + (relCode (scalarCode index s)).length ∧
    (circuitOf index s k).2.1 = nodeName (k + (relCode (scalarCode index s)).length - 1) ∧
    0 < (relCode (scalarCode index s)).length

/-- Opus A's `ExactQueryCode`, verbatim. -/
def ExactQueryCode : Prop :=
  ∀ (tag : Nat) {ι : Type} (index : ι → Nat) (sa sb : Scalar ι),
    ∃ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula),
      Topological known gs ∧ PlainPreparedFormula p ∧
      queryCode tag (scalarCode index sa) (scalarCode index sb) = encodeInput known gs p true ∧
      ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
        (HasSuccessfulObservation f gs p true ↔
          ∃ ν : Nat → Nat, (∀ n, 0 < ν n) ∧
            Counter tag (scalarValueWith f (fun x => ν (index x)) sa)
                        (scalarValueWith f (fun x => ν (index x)) sb))

def QueryCodeEffectivity : Prop := Primrec (fun x : Nat × Nat × Nat => queryCode x.1 x.2.1 x.2.2)

def FullGroundScalarCircuitCode : Prop :=
  CircuitCalibration ∧ ExactQueryCode ∧ QueryCodeEffectivity

end LogicLineages.PermittedControl.GroundScalarCircuit
