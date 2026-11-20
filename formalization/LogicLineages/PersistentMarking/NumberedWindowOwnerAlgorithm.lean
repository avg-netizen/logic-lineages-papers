module

public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
open NumberedWindowFieldAlgorithm (pack packNode)
open NumberedWindowAnnotationAlgorithm (arrow)

def owner (head label base extras output : Nat) :=
  packNode 5 [head,output,label,base,extras]

def copies (head label base extras : Nat) (domains : List Nat) :=
  pack (domains.map (owner head label base extras))

/-- Each application uses the codomain of its actual remaining arrow prefix. -/
def plan (result : Nat) (domains : List Nat) : Nat × List (Nat × Nat) :=
  domains.foldr (fun dom rest => (arrow dom rest.1,(dom,rest.1) :: rest.2)) (result,[])

def applyCopies (head label base extras selected : Nat) (steps : List (Nat × Nat)) :=
  steps.foldl (fun fn p => packNode 6 [p.1,p.2,fn,owner head label base extras p.1]) selected

end LogicLineages.PersistentMarking.NumberedWindowOwnerAlgorithm
