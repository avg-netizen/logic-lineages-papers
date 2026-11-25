module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastHeaderInvarianceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxProfileProof

open NumberedWindowFieldAlgorithm (unpack unpackNode)
open NumberedWindowExchangeAlgorithm (Row parts termNext bits row next table)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowScalarAlgorithm (Settings edge vertices least)
open NumberedWindowClassAlgorithm (rounds)
open NumberedWindowInternalSparsePathAdvanceTargets (packedLeast)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)
open NumberedWindowInternalLiteralLeastHeaderInvarianceProof (header roundsInvariant)

/-- The two annotations and leading function constructor of an
auxiliary survive exchange. The argument and the function themselves
are not required to stay literally unchanged. -/
def auxProfile (q : Nat) : Option (Nat × Nat × Option Nat) :=
  (unpackNode q).bind fun p =>
    if p.1 = 6 then some (p.2.getD 0 0,p.2.getD 1 0,header (p.2.getD 2 0)) else none

private theorem tableLength (hp : HeadPairs) (n : Nat) : (table hp n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier (hp : HeadPairs) {k n : Nat} (h : k < n) :
    (table hp n)[k]? = some (next hp (table hp k) k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : k < n
    · simp only [table,List.getElem?_append_left (tableLength hp n ▸ prior)]
      exact ih prior
    · have last : k = n := by omega
      subst k
      simpa only [table,tableLength] using
        (List.getElem?_concat_length (l := table hp n) (a := next hp (table hp n) n))

private theorem partSameHeader (hp : HeadPairs) (rows : List Row) (a b : Nat)
    (h : termNext hp rows a b = true) : header a = header b := by
  unfold termNext at h
  cases ha : unpackNode a with
  | none => simp [ha] at h
  | some r =>
    cases hb : unpackNode b with
    | none => simp [ha,hb] at h
    | some s =>
      have hh : parts hp rows r.1 s.1 r.2 s.2 = true := by simpa [ha,hb] using h
      have same : r.1 = s.1 := by
        by_contra neq
        simp [parts,neq] at hh
      simp [header,ha,hb,same]

private theorem selectedChildHeader (hp : HeadPairs) (n a b : Nat)
    (h : ((table hp n).getD (pair a b) (false,false)).1 = true) : header a = header b := by
  rw [List.getD_eq_getElem?_getD] at h
  by_cases inside : pair a b < n
  · rw [earlier hp inside] at h
    simp only [Option.getD_some,next,encodedPair,Option.map_some] at h
    exact partSameHeader hp (table hp (pair a b)) a b h
  · have absent : (table hp n)[pair a b]? = none := by
      apply List.getElem?_eq_none
      rw [tableLength]
      omega
    simp [absent] at h

private theorem fromParts (hp : HeadPairs) (n a b : Nat) (i j : Nat) (fs gs : List Nat)
    (ha : unpackNode a = some (i,fs)) (hb : unpackNode b = some (j,gs))
    (h : parts hp (table hp n) i j fs gs = true) : auxProfile a = auxProfile b := by
  have same : i = j := by
    by_contra neq
    simp [parts,neq] at h
  subst j
  by_cases aux : i = 6
  · subst i
    change ((fs.getD 0 0 == gs.getD 0 0) && (fs.getD 1 0 == gs.getD 1 0) &&
      ((((table hp n).getD (pair (fs.getD 2 0) (gs.getD 2 0)) (false,false)).1 &&
        (fs.getD 3 0 == gs.getD 3 0)) || ((fs.getD 2 0 == gs.getD 2 0) &&
        ((table hp n).getD (pair (fs.getD 3 0) (gs.getD 3 0)) (false,false)).1))) = true at h
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at h
    have funHeader : header (fs.getD 2 0) = header (gs.getD 2 0) := by
      rcases h.2 with move | keep
      · exact selectedChildHeader hp n _ _ move.1
      · exact congrArg header keep.1
    simp [auxProfile,ha,hb]
    simpa only [List.getD_eq_getElem?_getD] using And.intro h.1.1 (And.intro h.1.2 funHeader)
  · simp [auxProfile,ha,hb,aux]

theorem exact_LiteralScalarEdgeAuxProfile (s : Settings) (ctx : List Nat) (ty a b : Nat)
    (h : edge s ctx ty a b = true) : auxProfile a = auxProfile b := by
  simp only [edge,bits,row,next,encodedPair,Option.map_some,Option.getD_some,Bool.and_eq_true] at h
  have moved := h.1.1.2
  unfold termNext at moved
  cases ha : unpackNode a with
  | none => simp [ha] at moved
  | some p =>
    cases hb : unpackNode b with
    | none => simp [ha,hb] at moved
    | some q =>
      obtain ⟨i,fs⟩ := p
      obtain ⟨j,gs⟩ := q
      exact fromParts s.equivalentHeads (pair a b) a b i j fs gs ha hb
        (by simpa [ha,hb] using moved)

/-- The actual packed representative computation preserves the two
annotations and the top constructor of the function within tag six. -/
theorem exact_LiteralPackedLeastAuxProfile (s : Settings) (ctx ty a b : Nat)
    (h : packedLeast s ctx ty a = some b) : auxProfile a = auxProfile b := by
  unfold packedLeast at h
  cases hc : unpack ctx with
  | none => simp [hc] at h
  | some c =>
    have one : least s c ty a = some b := by simpa [hc] using h
    let pool := vertices s a
    change (rounds (edge s c ty) pool a pool.length).min? = some b at one
    exact roundsInvariant auxProfile (exact_LiteralScalarEdgeAuxProfile s c ty) pool a pool.length b
      (List.min?_eq_some_iff.mp one).1

#print axioms exact_LiteralScalarEdgeAuxProfile
#print axioms exact_LiteralPackedLeastAuxProfile
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastAuxProfileProof
