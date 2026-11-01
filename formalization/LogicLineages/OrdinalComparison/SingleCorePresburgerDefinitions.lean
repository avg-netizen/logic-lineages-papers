module
public import LogicLineages.OrdinalComparison.SingleCoreRowDefinitions
public import LogicLineages.OrdinalComparison.OneInputBooleanDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

inductive SingleCorePresburgerExpr where
  | truth (value : Bool)
  | equal (index value : Nat)
  | lower (index value : Nat)
  | conj (left right : SingleCorePresburgerExpr)
  | disj (left right : SingleCorePresburgerExpr)

def singleCorePresburgerValue : SingleCorePresburgerExpr → (Nat → Nat) → Bool
  | .truth b, _ => b
  | .equal i c, ρ => decide (ρ i=c)
  | .lower i c, ρ => decide (c≤ρ i)
  | .conj E F, ρ => singleCorePresburgerValue E ρ && singleCorePresburgerValue F ρ
  | .disj E F, ρ => singleCorePresburgerValue E ρ || singleCorePresburgerValue F ρ

def singleCorePresburgerVariables : SingleCorePresburgerExpr → List Nat
  | .truth _ => []
  | .equal i _ | .lower i _ => [i]
  | .conj E F | .disj E F => singleCorePresburgerVariables E++singleCorePresburgerVariables F

/-- Literal finite Presburger syntax: only original-variable equality and lower
constant bounds, combined by Boolean conjunction/disjunction. -/
def singleCorePresburgerEncode : SingleCorePresburgerExpr → List OneInputBooleanInstruction
  | .truth b => [(if b then 1 else 0,0,0)]
  | .equal i c => [(2,i,c)]
  | .lower i c => [(3,i,c)]
  | .conj E F => singleCorePresburgerEncode E++singleCorePresburgerEncode F++[(6,0,0)]
  | .disj E F => singleCorePresburgerEncode E++singleCorePresburgerEncode F++[(7,0,0)]

def singleCoreIntegerSign (z : Int) : Nat := if z<0 then 0 else if z=0 then 1 else 2

def singleCoreBoxWords (bound : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range (bound-1)).flatMap (fun value =>
      (singleCoreBoxWords bound n).map (fun word => (value+1)::word))

/-- First occurrence lookup respects repeated original variable names.
The complete point clause later enforces ALL occurrences simultaneously. -/
def singleCoreBoxLookup (support word : List Nat) (i : Nat) : Nat :=
  word.getD (support.findIdx (fun j => decide (j=i))) 1

def singleCoreBoxTuple (source : Nat) (support word : List Nat) : List Nat :=
  (List.range (source+1)).map (fun i => singleCoreBoxLookup support word i-1)

noncomputable def encodedSingleCoreRowPoint (row : EncodedSingleCoreRow) (t : Nat) : Nat :=
  let parts := encodedSingleCoreRowParts row
  comparisonNaturalSign (encodedPositiveEvaluation parts.1 t) (encodedPositiveEvaluation parts.2 t)

noncomputable def encodedSingleCoreBoxSign (source : Nat) (row : EncodedSingleCoreRow) (word : List Nat) : Nat :=
  let support := encodedSingleCoreSupport source
  let t := encodedSingleCoreEvaluation source (singleCoreBoxTuple source support word)
  encodedSingleCoreRowPoint row t

def singleCorePresburgerConstantCode (b : Bool) : List OneInputBooleanInstruction := [(if b then 1 else 0,0,0)]

def singleCorePresburgerTailCode (support : List Nat) (threshold : Nat) : List OneInputBooleanInstruction :=
  support.foldr (fun i rest => [(3,i,threshold)]++rest++[(7,0,0)]) (singleCorePresburgerConstantCode false)

def singleCorePresburgerPointCode (support word : List Nat) : List OneInputBooleanInstruction :=
  (List.range support.length).foldr
    (fun i rest => [(2,support.getD i 0,word.getD i 1)]++rest++[(6,0,0)])
    (singleCorePresburgerConstantCode true)

noncomputable def encodedSingleCorePresburger (source : Nat) (row : EncodedSingleCoreRow) (desired : Nat) :
    List OneInputBooleanInstruction :=
  let support := encodedSingleCoreSupport source
  let result := encodedSingleCoreRowSign row
  let tail := singleCorePresburgerTailCode support result.2++
    singleCorePresburgerConstantCode (decide (result.1=desired))++[(6,0,0)]
  let box := (singleCoreBoxWords result.2 support.length).foldr (fun word rest =>
    if encodedSingleCoreBoxSign source row word=desired then
      singleCorePresburgerPointCode support word++rest++[(7,0,0)] else rest)
    (singleCorePresburgerConstantCode false)
  tail++box++[(7,0,0)]

noncomputable def encodedSingleCoreUniversal (source : Nat) (row : EncodedSingleCoreRow) (allowed : List Nat) : Bool :=
  let support := encodedSingleCoreSupport source
  let result := encodedSingleCoreRowSign row
  (support.isEmpty || decide (result.1∈allowed)) &&
    (singleCoreBoxWords result.2 support.length).all (fun word => decide (encodedSingleCoreBoxSign source row word∈allowed))

end LogicLineages.OrdinalComparison
