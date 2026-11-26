module

public import LogicLineages.PersistentMarking.NumberedWindowCoverProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowProgramKernelChecks
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverLayerPrograms
open NumberedWindowCoverAlgorithm NumberedWindowFieldAlgorithm LogicLineages.ComputabilityKnowledge List.Vector

private theorem pairPrim : Primrec₂ NumberedWindowPairAlgorithm.pair := by
  obtain ⟨p,h⟩ := NumberedWindowProgramKernelChecks.polynomial
  apply ((GorbowPRProgram.Proof.primitiveEvaluation 2 p).comp
    (Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp Primrec.snd (Primrec.const List.Vector.nil)))).of_eq
  rintro ⟨a,b⟩
  exact h a b

private theorem nodePrim : Primrec₂ packNode := by
  obtain ⟨p,h⟩ := NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.1
  apply ((GorbowPRProgram.Proof.primitiveEvaluation 2 p).comp
    (Primrec.vector_cons.comp Primrec.fst (Primrec.vector_cons.comp (Primrec.encode.comp Primrec.snd) (Primrec.const List.Vector.nil)))).of_eq
  rintro ⟨a,bs⟩
  exact h a bs

private def combinations : List (List Nat) → List (List Nat)
  | [] => [[]]
  | axis :: rest => axis.flatMap (fun n => (combinations rest).map (fun ns => n :: ns))

private theorem combinationsPrim : Primrec combinations := by
  let appendAxis (axis : List Nat) (tails : List (List Nat)) := axis.flatMap (fun n => tails.map (fun ns => n :: ns))
  have combine : Primrec₂ appendAxis := Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst) (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂
  have fold := Primrec.list_foldr (Primrec.id : Primrec (fun x : List (List Nat) => x))
    (Primrec.const ([[]] : List (List Nat))) (combine.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply fold.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change List.foldr appendAxis [[]] xs = combinations xs at ih
    change appendAxis a (List.foldr appendAxis [[]] xs) = _
    rw [ih]
    rfl

private def nodes (tag : Nat) (axes : List (List Nat)) :=
  (combinations axes).map (packNode tag)

private theorem nodesPrim (tag : Nat) : Primrec (nodes tag) :=
  Primrec.list_map combinationsPrim (nodePrim.comp (Primrec.const tag) Primrec.snd).to₂

private theorem axis {α} [Primcodable α] {a : α → List Nat} {xs : α → List (List Nat)}
    (ha : Primrec a) (hs : Primrec xs) : Primrec (fun x => a x :: xs x) := Primrec.list_cons.comp ha hs

abbrev Input := List Nat × List Nat × Nat
abbrev Layer := List Nat × List Nat

theorem layerPrim : Primrec (fun p : Input × Layer =>
    (leaves p.1.2.1 (List.range (p.1.2.2+1)) ++ lambdas p.1.2.1 p.2.1 ++ ordinary p.1.1 p.2.2 ++
      numbered p.1.1 p.1.2.1 (List.range (p.1.2.2+1)) p.2.2 ++ applications p.1.2.1 p.2.1,
     cells p.2.1 p.2.2)) := by
  have H : Primrec (fun p : Input × Layer => p.1.1) := Primrec.fst.comp Primrec.fst
  have K : Primrec (fun p : Input × Layer => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ids : Primrec (fun p : Input × Layer => List.range (p.1.2.2+1)) := Primrec.list_range.comp
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ts : Primrec (fun p : Input × Layer => p.2.1) := Primrec.fst.comp Primrec.snd
  have args : Primrec (fun p : Input × Layer => p.2.2) := Primrec.snd.comp Primrec.snd
  let stop : Primrec (fun _ : Input × Layer => ([] : List (List Nat))) := Primrec.const []
  have leaf := Primrec.list_append.comp (Primrec.list_append.comp
    ((nodesPrim 0).comp (axis K (axis ids stop))) ((nodesPrim 1).comp (axis K (axis ids stop))))
    ((nodesPrim 3).comp (axis K stop))
  have ls := (nodesPrim 2).comp (axis K (axis ts stop))
  have os := (nodesPrim 4).comp (axis H (axis args stop))
  have ns := (nodesPrim 5).comp (axis H (axis K (axis ids (axis args (axis args stop)))))
  have apps := (nodesPrim 6).comp (axis K (axis K (axis ts (axis ts stop))))
  have rawTerms := Primrec.list_append.comp (Primrec.list_append.comp (Primrec.list_append.comp
    (Primrec.list_append.comp leaf ls) os) ns) apps
  have tail := Primrec.list_flatMap ts (Primrec.list_map (args.comp Primrec.fst)
    (Primrec.succ.comp (pairPrim.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂).to₂
  apply (rawTerms.pair (Primrec.list_cons.comp (Primrec.const 0) tail)).of_eq
  intro p
  simp [nodes,combinations,leaves,namedLeaves,lambdas,ordinary,numbered,applications,cells,
    List.map_flatMap,List.map_map,Function.comp_def]

end LogicLineages.PersistentMarking.NumberedWindowCoverLayerPrograms
