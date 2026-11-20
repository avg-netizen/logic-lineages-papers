module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicLeastExchangeProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicLeastTargets
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView)
open NumberedWindowScalarAlgorithm (Settings edge)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowExchangeAlgorithm (Row parts termNext bits row next)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)

private theorem sourceParts (hp : HeadPairs) (rows : List Row) (leaf tag : Nat)
    (fs gs : List Nat) (atom : leaf = 0 ∨ leaf = 3) :
    parts hp rows leaf tag fs gs = false := by
  rcases atom with rfl | rfl <;> simp [parts]

private theorem targetParts (hp : HeadPairs) (rows : List Row) (leaf tag : Nat)
    (fs gs : List Nat) (atom : leaf = 0 ∨ leaf = 3) :
    parts hp rows tag leaf fs gs = false := by
  by_cases eq : tag = leaf
  · rw [eq]
    exact sourceParts hp rows leaf leaf fs gs atom
  · simp [parts,eq]

private theorem termRows (hp : HeadPairs) (rows : List Row) (q x tag : Nat) (fs : List Nat)
    (view : unpackNode q = some (tag,fs)) (atom : tag = 0 ∨ tag = 3) :
    termNext hp rows q x = false ∧ termNext hp rows x q = false := by
  cases found : unpackNode x with
  | none => simp [termNext,view,found]
  | some other =>
    rcases other with ⟨i,gs⟩
    simp [termNext,view,found,sourceParts hp rows tag i fs gs atom,
      targetParts hp rows tag i gs fs atom]

theorem exchangeRows : ExactAtomicExchangeRows := by
  constructor
  · intro hp rows t n x
    exact termRows hp rows (freeRaw t n) x 0 [t,n] (freeView t n) (Or.inl rfl)
  · intro hp rows t x
    exact termRows hp rows (bottomRaw t) x 3 [t] (bottomView t) (Or.inr rfl)

/-- Do not evaluate the finite table on a symbolic number: the literal
row calculation has the same rejected atom in every possible prior table. -/
private theorem noScalarEdge (s : Settings) (Γ : List Nat) (requested q x : Nat)
    (rows : ∀ prev, termNext s.equivalentHeads prev q x = false) :
    edge s Γ requested q x = false := by
  simp [edge,bits,row,next,encodedPair,rows]

theorem scalarIsolation : ExactAtomicScalarEdgeIsolation := by
  intro s Γ requested t
  constructor
  · intro n x
    exact ⟨noScalarEdge s Γ requested (freeRaw t n) x
      (fun prev => (exchangeRows.1 s.equivalentHeads prev t n x).1),
      noScalarEdge s Γ requested x (freeRaw t n)
        (fun prev => (exchangeRows.1 s.equivalentHeads prev t n x).2)⟩
  · intro x
    exact ⟨noScalarEdge s Γ requested (bottomRaw t) x
      (fun prev => (exchangeRows.2 s.equivalentHeads prev t x).1),
      noScalarEdge s Γ requested x (bottomRaw t)
        (fun prev => (exchangeRows.2 s.equivalentHeads prev t x).2)⟩

end LogicLineages.PersistentMarking.NumberedWindowAtomicLeastExchangeProof
