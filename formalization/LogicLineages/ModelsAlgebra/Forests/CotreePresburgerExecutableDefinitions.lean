module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerFiniteDecisionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductiveStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProductStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerTransitionStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable
open FirstOrder Language RankedParse ProfileAutomatonEncoding CotreePresburger
open CotreePresburgerBoolean CotreePresburgerProduct CotreePresburgerTransition

/-- Exactly the finite source productivity query: one of the two operations,
at least two children, and no child outside the already productive set. -/
def query {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) (R : Finset Q) (q : Q) : PFormula Q :=
  (A.node .union q ⊔ A.node .join q) ⊓
    (positive (totalTerm (A := Q)) ⊓ ((totalTerm (A := Q)).equal 1).not) ⊓
    allOf (fun s : Q => (truth (s ∉ R)).imp ((.var s : PTerm Q).equal 0))

def enabled {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) (R : Finset Q) (q : Q) : Bool :=
  CotreePresburgerFiniteDecision.satisfiable (query A R q)

def step {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) (R : Finset Q) : Finset Q :=
  R ∪ {A.leaf} ∪ Finset.univ.filter (fun q => enabled A R q = true)

def reachable {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) : Nat → Finset Q
  | 0 => ∅
  | n + 1 => step A (reachable A n)

def productive {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) : Finset Q :=
  reachable A (Fintype.card Q)

/-- Tests absence of an accepting productive run. For arbitrary automata this
is not automatically reduced-domain emptiness; the fixed source target below
uses the already proved source automata guards. -/
def noAcceptingRun {Q : Type} [Fintype Q] [LinearOrder Q] (A : Automaton Q) : Bool :=
  (elements Q).all (fun q => decide (q ∈ productive A → A.accept q = false))

def inclusion (M N : Machine) [LinearOrder M.State] [LinearOrder N.State] : Bool :=
  noAcceptingRun (difference (source M) (source N))
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerExecutable
