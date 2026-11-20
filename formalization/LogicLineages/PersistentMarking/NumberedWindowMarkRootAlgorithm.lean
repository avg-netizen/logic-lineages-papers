module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm
open NumberedWindowFieldAlgorithm (packNode unpackNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowAnnotationAlgorithm (annotations declaration)

def guarded (src dst : Nat) (v : Bool) := (syntaxBits src).1 && (syntaxBits dst).1 && v

def markBody (k dst : Nat) (p : Nat × List Nat) :=
  let f := p.2.getD 0 0
  let base := p.2.getD 1 0
  p.1 == 4 && packNode 5 [f,(declaration f).1,k,base,0] == dst

def lowerBody (dst : Nat) (p : Nat × List Nat) :=
  let val (i : Nat) := p.2.getD i 0
  p.1 == 5 && val 2 != 0 && packNode 5 [val 0,val 1,(val 2).pred,val 3,val 4] == dst

def mark (k src dst : Nat) := guarded src dst ((unpackNode src).any (markBody k dst))
def lower (src dst : Nat) := guarded src dst ((unpackNode src).any (lowerBody dst))
def bottom (src dst : Nat) :=
  let target := packNode 3 [(annotations src).1]
  guarded src dst (src != target && target == dst)
end LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm
