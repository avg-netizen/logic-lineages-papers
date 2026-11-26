module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (row)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowScalarAlgorithm (Settings admitted edge least)
open NumberedWindowClassAlgorithm (rounds)
open NumberedWindowAddressApplication (graph arrowView)

/-- One literal raw auxiliary application over a bare atom, not any
term that happens to have a neutral-looking interpreted head. -/
inductive AtomHead : Nat → Prop where
  | free (t n : Nat) : AtomHead (freeRaw t n)
  | bottom (t : Nat) : AtomHead (bottomRaw t)

def auxRaw (dom cod fn arg : Nat) : Nat := packNode 6 [dom,cod,fn,arg]

/-- An ordered argument trace through the actual original child rows.
It is not equality of representatives, symmetry, or a new checker. -/
inductive ArgumentMoves (hp : HeadPairs) : Nat → Nat → Prop where
  | empty (a : Nat) : ArgumentMoves hp a a
  | snoc {a b c : Nat} :
      ArgumentMoves hp a b → (row hp b c).1 = true → ArgumentMoves hp a c

/-- Both orientations of the actual original raw row, tested against a
potentially arbitrary candidate q with its actual syntax bit. Exact
tag6/dom/cod/function survives. A genuine nontrivial row changes only
the argument through the actual earlier-table child row. -/
def ExactAtomicAuxExchange : Prop :=
  ∀ (hp : HeadPairs) dom cod fn arg q, AtomHead fn → (syntaxBits q).1 = true →
    ((row hp (auxRaw dom cod fn arg) q).1 = true →
      ∃ a, q = auxRaw dom cod fn a ∧ (row hp arg a).1 = true) ∧
    ((row hp q (auxRaw dom cod fn arg)).1 = true →
      ∃ a, q = auxRaw dom cod fn a ∧ (row hp a arg).1 = true)

/-- The complete actual edge bit supplies the syntax/actual window on
the same candidate, without caller syntax or admission premises. -/
def ExactAtomicAuxScalarEdges : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested dom cod fn arg q, AtomHead fn →
    (edge s Γ requested (auxRaw dom cod fn arg) q = true →
      ∃ a, q = auxRaw dom cod fn a ∧ (row s.equivalentHeads arg a).1 = true ∧
        admitted s Γ requested q = true) ∧
    (edge s Γ requested q (auxRaw dom cod fn arg) = true →
      ∃ a, q = auxRaw dom cod fn a ∧ (row s.equivalentHeads a arg).1 = true ∧
        admitted s Γ requested q = true)

/-- Keep original rounds for arbitrary actual pool and fuel. Stutters
are allowed and do not create a nonexistent edge. The ordered
argument path is oriented in the same direction as the original
rounds, including the reverse recognition from an output in the fiber. -/
def ExactAtomicAuxFiniteRounds : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested dom cod fn arg,
    AtomHead fn → ∀ (pool : List Nat) (fuel q : Nat),
    (q ∈ rounds (edge s Γ requested) pool (auxRaw dom cod fn arg) fuel →
      ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads arg a) ∧
    (auxRaw dom cod fn arg ∈ rounds (edge s Γ requested) pool q fuel →
      ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads a arg)

/-- Conditional Some statements for the actual least (original
vertices, original bounded rounds and min?). No least existence,
type narrowing, scalar fixed point or symmetry conclusion. -/
def ExactAtomicAuxLeast : Prop :=
  ∀ (s : Settings) (Γ : List Nat) requested dom cod fn arg q, AtomHead fn →
    (least s Γ requested (auxRaw dom cod fn arg) = some q →
      ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads arg a) ∧
    (least s Γ requested q = some (auxRaw dom cod fn arg) →
      ∃ a, q = auxRaw dom cod fn a ∧ ArgumentMoves s.equivalentHeads a arg)

/-- Whole actual original application at a literal atomic-head address.
The supplied argument and returned value are the same actual raw
codes, in the same raw packed context. The output raw application
retains the exact original bare function and a possibly exchanged
representative of the actual original supplied argument. -/
def ExactAtomicAuxOriginalApplication : Prop :=
  ∀ (s : Settings) rawCtx functionType fn argument value, AtomHead fn →
    graph s (packedAddress rawCtx functionType fn) argument value = true →
    ∃ dom cod a a',
      arrowView functionType = some (dom,cod) ∧
      argument = packedAddress rawCtx dom a ∧
      value = packedAddress rawCtx cod (auxRaw dom cod fn a') ∧
      ArgumentMoves s.equivalentHeads a a'

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets
