module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutableDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.Targets
open FirstOrder Language RankedParse ProfileAutomatonEncoding CotreePresburgerBoolean CotreePresburgerProduct

def QueryExact : Prop := ∀ (Q : Type) [Fintype Q] [LinearOrder Q]
    (A : Automaton Q) (R : Finset Q) q (counts : Q → Nat),
  Formula.Realize (query A R q) counts ↔
    (∃ o, Formula.Realize (A.node o q) counts) ∧ 2 ≤ ∑ s, counts s ∧
      ∀ s, s ∉ R → counts s = 0

def EnabledExact : Prop := ∀ (Q : Type) [Fintype Q] [LinearOrder Q]
    (A : Automaton Q) (R : Finset Q) q,
  enabled A R q = true ↔ CotreePresburgerProductive.Enabled A R q

def ReachableExact : Prop := ∀ (Q : Type) [Fintype Q] [LinearOrder Q]
    (A : Automaton Q) n,
  reachable A n = CotreePresburgerProductive.reachable A n

def ProductiveExact : Prop := ∀ (Q : Type) [Fintype Q] [LinearOrder Q]
    (A : Automaton Q) q,
  q ∈ productive A ↔ ∃ C, Runs A C q

def SourceEmptyExact : Prop := ∀ (M N : Machine) [LinearOrder M.State] [LinearOrder N.State],
  noAcceptingRun (difference (source M) (source N)) = true ↔
    Empty (difference (source M) (source N))

def SourceInclusionExact : Prop := ∀ (M N : Machine) [LinearOrder M.State] [LinearOrder N.State],
  inclusion M N = true ↔ ∀ C, Language (source M) C → Language (source N) C
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable.Targets
