module

public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
open NumberedWindowFieldAlgorithm (unpack unpackNode pack packNode)
open NumberedWindowExchangeAlgorithm (Row parts termNext bits row next table)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowScalarAlgorithm (Settings edge vertices least)
open NumberedWindowClassAlgorithm (advance rounds)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowAtomicRawStepFieldProof (codeOfNode)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (headTailOfCell cellAt)

/-- Keep the original optional decoded header, including invalid
inputs. No default numeral is inserted for an invalid node. -/
def header (q : Nat) : Option Nat := (unpackNode q).map Prod.fst

private theorem termNextSameHeader (hp : HeadPairs) (rows : List Row) (a b : Nat)
    (held : termNext hp rows a b = true) :
    ∃ (tag : Nat) (l r : List Nat), unpackNode a = some (tag,l) ∧ unpackNode b = some (tag,r) := by
  unfold termNext at held
  cases ha : unpackNode a with
  | none => simp [ha] at held
  | some va =>
    cases hb : unpackNode b with
    | none => simp [ha,hb] at held
    | some vb =>
      obtain ⟨i,as⟩ := va
      obtain ⟨j,bs⟩ := vb
      have h : parts hp rows i j as bs = true := by simpa [ha,hb] using held
      by_cases same : i = j
      · subst j
        exact ⟨i,as,bs,rfl,rfl⟩
      · simp [parts,same] at h

private theorem scalarEdgeSameHeader (s : Settings) (ctx : List Nat) (t a b : Nat)
    (held : edge s ctx t a b = true) :
    ∃ (tag : Nat) (l r : List Nat), unpackNode a = some (tag,l) ∧ unpackNode b = some (tag,r) := by
  simp only [edge,bits,row,next,encodedPair,Option.map_some,Option.getD_some,Bool.and_eq_true] at held
  exact termNextSameHeader s.equivalentHeads (table s.equivalentHeads (pair a b)) a b held.1.1.2

theorem exact_LiteralScalarEdgeHeader (s : Settings) (ctx : List Nat) (t a b : Nat)
    (held : edge s ctx t a b = true) : header a = header b := by
  obtain ⟨tag,l,r,ha,hb⟩ := scalarEdgeSameHeader s ctx t a b held
  simp only [header,ha,hb,Option.map_some]

private theorem rawCodeAtNode (tag : Nat) (fs : List Nat) :
    run cellHead (packNode tag fs) = tag :=
  (headTailOfCell (cellAt tag (pack fs))).1

theorem exact_LiteralScalarEdgeCellHead (s : Settings) (ctx : List Nat) (t a b : Nat)
    (held : edge s ctx t a b = true) : run cellHead a = run cellHead b := by
  obtain ⟨tag,l,r,ha,hb⟩ := scalarEdgeSameHeader s ctx t a b held
  rw [codeOfNode ha,codeOfNode hb,rawCodeAtNode,rawCodeAtNode]

theorem roundsInvariant {δ : Type} {E : Nat → Nat → Bool} (F : Nat → δ)
    (preserves : ∀ a b, E a b = true → F a = F b)
    (pool : List Nat) (seed fuel out : Nat)
    (held : out ∈ rounds E pool seed fuel) : F seed = F out := by
  induction fuel generalizing out with
  | zero =>
    simp only [rounds,List.mem_filter,beq_iff_eq] at held
    rw [held.2]
  | succ fuel ih =>
    change out ∈ advance E pool (rounds E pool seed fuel) at held
    simp only [advance,List.mem_filter,List.any_eq_true,Bool.or_eq_true,beq_iff_eq] at held
    obtain ⟨w,seen,move⟩ := held.2
    have start := ih w seen
    rcases move with same | hit
    · exact start.trans (congrArg F same)
    · exact start.trans (preserves w out hit)

theorem exact_LiteralLeastHeader (s : Settings) (ctx : List Nat) (t q out : Nat)
    (held : least s ctx t q = some out) : header q = header out := by
  let pool := vertices s q
  change (rounds (edge s ctx t) pool q pool.length).min? = some out at held
  exact roundsInvariant header (exact_LiteralScalarEdgeHeader s ctx t) pool q pool.length out
    (List.min?_eq_some_iff.mp held).1

/-- Every original successful packed least answer retains its input
literal constructor. This is a numeric calibration seam for choosing
a corresponding internal header-checking AST, not an open rule. -/
theorem exact_LiteralPackedLeastHeader (s : Settings) (ctx ty q out : Nat)
    (held : packedLeast s ctx ty q = some out) : header q = header out := by
  unfold packedLeast at held
  cases h : unpack ctx with
  | none => simp [h] at held
  | some c =>
    exact exact_LiteralLeastHeader s c ty q out (by simpa [h] using held)

/-- The actual primitive cell-head values coincide on every selected
packed least answer, even if an invalid seed was retained without an
edge. Every real exchange edge has an actual matching decoded header;
the zero-edge case preserves the exact seed. -/
theorem exact_LiteralPackedLeastCellHead (s : Settings) (ctx ty q out : Nat)
    (held : packedLeast s ctx ty q = some out) : run cellHead q = run cellHead out := by
  unfold packedLeast at held
  cases h : unpack ctx with
  | none => simp [h] at held
  | some c =>
    have one : least s c ty q = some out := by simpa [h] using held
    let pool := vertices s q
    change (rounds (edge s c ty) pool q pool.length).min? = some out at one
    exact roundsInvariant (run cellHead) (exact_LiteralScalarEdgeCellHead s c ty) pool q pool.length out
      (List.min?_eq_some_iff.mp one).1

#print axioms exact_LiteralScalarEdgeHeader
#print axioms exact_LiteralScalarEdgeCellHead
#print axioms exact_LiteralPackedLeastCellHead
#print axioms exact_LiteralLeastHeader
#print axioms exact_LiteralPackedLeastHeader
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
