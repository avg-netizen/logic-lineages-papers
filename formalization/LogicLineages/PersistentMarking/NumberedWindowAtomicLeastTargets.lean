module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicLeastTargets
open NumberedWindowAtomicRawStep
open NumberedWindowScalarAlgorithm (Settings edge least)
open NumberedWindowExchangeAlgorithm (Row termNext)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowClassAlgorithm (rounds)

/-- Preserve both orientations of the literal original exchange-table
row, independently of its previous finite table and head settings. -/
def ExactAtomicExchangeRows : Prop :=
  (∀ (hp : HeadPairs) (rows : List Row) t n x,
    termNext hp rows (freeRaw t n) x = false ∧ termNext hp rows x (freeRaw t n) = false) ∧
  (∀ (hp : HeadPairs) (rows : List Row) t x,
    termNext hp rows (bottomRaw t) x = false ∧ termNext hp rows x (bottomRaw t) = false)

def Isolated (s : Settings) (Γ : List Nat) (requested atom : Nat) : Prop :=
  ∀ x, edge s Γ requested atom x = false ∧ edge s Γ requested x atom = false

def ExactAtomicScalarEdgeIsolation : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested t,
    (∀ n, Isolated s Γ requested (freeRaw t n)) ∧ Isolated s Γ requested (bottomRaw t)

def RoundSingleton (s : Settings) (Γ : List Nat) (requested atom : Nat) : Prop :=
  ∀ (pool : List Nat) (fuel seed out : Nat),
    (atom ∈ rounds (edge s Γ requested) pool seed fuel → seed = atom) ∧
    (out ∈ rounds (edge s Γ requested) pool atom fuel → out = atom)

/-- These are the literal original bounded rounds, for every raw pool.
Claim only conditional membership, not that a pool contains the atom. -/
def ExactAtomicRoundSingleton : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested t,
    (∀ n, RoundSingleton s Γ requested (freeRaw t n)) ∧
    RoundSingleton s Γ requested (bottomRaw t)

def LeastSingleton (s : Settings) (Γ : List Nat) (requested atom : Nat) : Prop :=
  (∀ q, least s Γ requested q = some atom → q = atom) ∧
  ∀ y, least s Γ requested atom = some y → y = atom

/-- Actual original pool/round count/min? of the original least program,
with no nonfailure or symmetry assumption. Requested type is independent
of the stored raw term type. -/
def ExactAtomicLeastSingleton : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested t,
    (∀ n, LeastSingleton s Γ requested (freeRaw t n)) ∧
    LeastSingleton s Γ requested (bottomRaw t)

end LogicLineages.PersistentMarking.NumberedWindowAtomicLeastTargets
