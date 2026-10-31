module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealCompletionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite
open RankedParse ProfileAutomatonEncoding ProfileLanguageEmpty RankedIdealCompletion

def successors (M : Machine) [DecidableEq M.State] (x : M.State) : Finset M.State :=
  if x ∈ productive M then operations.biUnion (fun o =>
    (productive M).biUnion (fun z => {M.node o x z, M.node o z x})) else ∅

def step (M : Machine) [DecidableEq M.State] (S : Finset M.State) : Finset M.State :=
  S ∪ S.biUnion (successors M)

def steps (M : Machine) [DecidableEq M.State] (S : Finset M.State) : Nat → Finset M.State
  | 0 => S
  | n+1 => step M (steps M S n)

def close (M : Machine) [DecidableEq M.State] (S : Finset M.State) : Finset M.State :=
  steps M S (Fintype.card M.State)

inductive Closure (M : Machine) [DecidableEq M.State] (S : Finset M.State) : M.State → Prop where
  | seed {q} : q ∈ S → Closure M S q
  | edge {q r} : Closure M S q → Epsilon M q r → Closure M S r

def nodeSeeds (M : Machine) [DecidableEq M.State] (o : Operation)
    (S T : Finset M.State) : Finset M.State :=
  (S ∩ productive M).biUnion (fun x => (T ∩ productive M).image (M.node o x))

def evaluate (M : Machine) [DecidableEq M.State] : Term → Finset M.State
  | .atom => close M {M.leaf}
  | .node o l r => close M (nodeSeeds M o (evaluate M l) (evaluate M r))

def accepts (M : Machine) [DecidableEq M.State] (t : Term) : Bool :=
  decide (∃ q ∈ evaluate M t, M.accept q = true)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealFinite
