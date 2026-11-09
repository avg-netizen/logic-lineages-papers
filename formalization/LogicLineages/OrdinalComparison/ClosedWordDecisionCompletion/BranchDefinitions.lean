module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportDefinitions
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueDefinitions
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion

/-- The actual distinct raw names, not word-value parameters or growth labels. -/
def names (p : Formula) : List Nat := p.variables.dedup

/-- The floor is internal branch bookkeeping. It starts at zero and prevents
later prefix evaluation below the tail where generated words were introduced. -/
noncomputable def SatisfiableAt (floor : Nat) (p : Formula) : Prop :=
  ∃ ν : Nat → Nat, (∀ i ∈ p.variables, floor ≤ ν i) ∧
    Formula.meaningful p ν ∧ Formula.eval ν p

def residueAtom : Atom → Atom
  | .nonnegative r => .nonnegative r
  | .divisible m r => .divisible m (WordResidue.row (m+1) r)

/-- Only congruences change. All Boolean constructors and original raw names
are literal, including zero-coefficient and repeated occurrences. -/
def residue : Formula → Formula
  | .bot => .bot
  | .top => .top
  | .atom a => .atom (residueAtom a)
  | .neg p => .neg (residue p)
  | .conj p q => .conj (residue p) (residue q)
  | .disj p q => .disj (residue p) (residue q)

def residueAtomTail : Atom → Nat
  | .nonnegative _ => 0
  | .divisible m r => WordResidue.rowTail (m+1) r

def residueTail (p : Formula) : Nat :=
  Algorithm.foldMax (p.atoms.map residueAtomTail)

noncomputable def matrix (D maximum : Nat) (p : Formula) : OutcomeTransport.Matrix :=
  OutcomeTransport.compile D maximum (residue p)

/-- Pay the old floor, ALL original word domains, all congruence residues,
and every actual guarded matrix before splitting the original current p. -/
noncomputable def commonTail (D floor : Nat) (p : Formula) : Nat :=
  max floor (max (OutcomeTransport.originalTail p)
    (max (residueTail p) (Algorithm.foldMax ((names p).map
      (fun maximum => (matrix D maximum p).tail)))))

def lowerRow (N i : Nat) : Row := (-(N : Int),[(1,(i,[]))])
def maximumRow (maximum i : Nat) : Row := (0,[(1,(maximum,[])),(-1,(i,[]))])

def frame (N maximum : Nat) (ns : List Nat) : Formula :=
  ns.foldr (fun i p => .conj (.atom (.nonnegative (lowerRow N i)))
    (.conj (.atom (.nonnegative (maximumRow maximum i))) p)) .top

abbrev Branch := Nat × Formula

/-- Evaluate only literal words of the original current matrix, and only
at or above its inherited floor. Check every removed occurrence's domain. -/
noncomputable def prefixChildren (floor N : Nat) (p : Formula) : List Branch :=
  (names p).flatMap (fun x => (List.range (N-floor)).filterMap (fun k =>
    let n := floor+k
    if OriginalWordEvaluation.removedDomains x n p then
      some (floor,OriginalWordEvaluation.specialize x n p) else none))

/-- The selected maximum is an actual original raw name. Every guarded case
is retained, even when inconsistent; only that raw name is quantified away. -/
noncomputable def highChildren (D N : Nat) (p : Formula) : List Branch :=
  (names p).flatMap (fun maximum => (matrix D maximum p).cases.map (fun q =>
    (N,WordLinearDecisionCompletion.eliminate maximum
      (.conj (frame N maximum (names p)) q))))

noncomputable def children (D floor : Nat) (p : Formula) : List Branch :=
  let N := commonTail D floor p
  prefixChildren floor N p ++ highChildren D N p

namespace Code

def «variables» (code : Nat) : List Nat :=
  (LinearRows.Code.atoms code).flatMap (fun payload =>
    rowVariables (WordLinearDecisionCompletion.Code.decodeAtom payload).2.2)

def names (code : Nat) : List Nat := (Code.variables code).dedup

def residueAtom (a : WordLinearDecisionCompletion.Code.AtomData) :
    WordLinearDecisionCompletion.Code.AtomData :=
  if a.1 = 0 then a else (a.1,a.2.1,WordResidue.row (a.2.1+1) a.2.2)

def residue (code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (fun payload => Encodable.encode
    (residueAtom (WordLinearDecisionCompletion.Code.decodeAtom payload))) code

def residueTail (code : Nat) : Nat :=
  Algorithm.foldMax ((LinearRows.Code.atoms code).map (fun payload =>
    let a := WordLinearDecisionCompletion.Code.decodeAtom payload
    if a.1 = 0 then 0 else WordResidue.rowTail (a.2.1+1) a.2.2))

noncomputable def matrix (D maximum code : Nat) : Nat × List Nat :=
  OutcomeTransport.Code.compile D maximum (residue code)

noncomputable def commonTail (D floor code : Nat) : Nat :=
  max floor (max (OutcomeTransport.Code.originalTail code)
    (max (residueTail code) (Algorithm.foldMax ((names code).map
      (fun maximum => (matrix D maximum code).1)))))

def nonnegative (r : Row) : Nat :=
  6*Encodable.encode ((0,0,r) : WordLinearDecisionCompletion.Code.AtomData)+2

def frame (N maximum : Nat) (ns : List Nat) : Nat :=
  ns.foldr (fun i p => LinearRows.Code.conjunction (nonnegative (lowerRow N i))
    (LinearRows.Code.conjunction (nonnegative (maximumRow maximum i)) p)) 0

noncomputable def prefixChildren (floor N code : Nat) : List (Nat × Nat) :=
  (names code).flatMap (fun x => (List.range (N-floor)).filterMap (fun k =>
    let n := floor+k
    if OriginalWordEvaluation.Code.removedDomains x n code then
      some (floor,OriginalWordEvaluation.Code.specialize x n code) else none))

noncomputable def highChildren (D N code : Nat) : List (Nat × Nat) :=
  (names code).flatMap (fun maximum => (matrix D maximum code).2.map (fun q =>
    (N,WordLinearDecisionCompletion.Code.eliminate maximum
      (LinearRows.Code.conjunction (frame N maximum (names code)) q))))

noncomputable def children (D floor code : Nat) : List (Nat × Nat) :=
  let N := commonTail D floor code
  prefixChildren floor N code ++ highChildren D N code

end Code
end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion
