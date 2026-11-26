module

public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowPairAlgorithm (pair)

def namedLeaves (tag : Nat) (K ids : List Nat) : List Nat :=
  K.flatMap (fun ty => ids.map (fun i => packNode tag [ty,i]))

def leaves (K ids : List Nat) :=
  namedLeaves 0 K ids ++ namedLeaves 1 K ids ++ K.map (fun ty => packNode 3 [ty])

def lambdas (K terms : List Nat) :=
  K.flatMap (fun ty => terms.map (fun q => packNode 2 [ty,q]))

def ordinary (H args : List Nat) :=
  H.flatMap (fun h => args.map (fun bs => packNode 4 [h,bs]))

def numbered (H K ids args : List Nat) :=
  H.flatMap (fun h => K.flatMap (fun ty => ids.flatMap (fun k =>
    args.flatMap (fun bs => args.map (fun es => packNode 5 [h,ty,k,bs,es])))))

def applications (K terms : List Nat) :=
  K.flatMap (fun s => K.flatMap (fun t => terms.flatMap (fun q =>
    terms.map (fun a => packNode 6 [s,t,q,a]))))

def cells (terms args : List Nat) :=
  0 :: terms.flatMap (fun q => args.map (fun as => pair q as + 1))

def grammar (H K : List Nat) (maxNumeral : Nat) : Nat → List Nat × List Nat
  | 0 => ([],[0])
  | depth+1 =>
    let (ts,as) := grammar H K maxNumeral depth
    let ids := List.range (maxNumeral+1)
    (leaves K ids ++ lambdas K ts ++ ordinary H as ++ numbered H K ids as ++ applications K ts,
     cells ts as)
end LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm
