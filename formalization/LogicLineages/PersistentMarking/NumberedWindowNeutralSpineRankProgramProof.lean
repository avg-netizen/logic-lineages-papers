module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
import LogicLineages.PersistentMarking.NumberedWindowFieldProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowHeadDeclarationPrograms
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowNeutralSpineRankAlgorithm
open NumberedWindowHeadDeclarationPrograms (choose)
open NumberedWindowFieldAlgorithm (unpackNode)

private theorem rowPrim : Primrec (fun p : List Nat × Nat × List Nat => row p.1 p.2.1 p.2.2) := by
  let T := List Nat × Nat × List Nat
  have tag : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have fs : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have len := Primrec.list_length.comp fs
  have child := (Primrec.list_getD (0 : Nat)).comp fs (Primrec.const 2)
  have prior : Primrec (fun p : T => p.1.getD (p.2.2.getD 2 0) 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.fst child
  have bump := choose prior 0 (Primrec.const (0 : Nat)) (Primrec.succ.comp prior)
  apply (choose tag 0 (choose len 2 (Primrec.const (2 : Nat)) (Primrec.const 0))
    (choose tag 3 (choose len 1 (Primrec.const (1 : Nat)) (Primrec.const 0))
      (choose tag 6 (choose len 4 bump (Primrec.const 0)) (Primrec.const 0)))).of_eq
  rintro ⟨xs,t,fields⟩
  by_cases ht : t = 0
  · subst t; simp [row]
  by_cases ht' : t = 3
  · subst t; simp [row]
  by_cases ht'' : t = 6
  · subst t; simp [row]
  simp [row,ht,ht',ht'']

private theorem nextPrim : Primrec₂ next := by
  have node : Primrec unpackNode := Primrec.encode_iff.mp
    ((GorbowPRProgram.Proof.unaryCorrespondence _).mpr NumberedWindowFieldProgramChecks.exact_TaggedNodePrograms.2)
  exact Primrec.option_getD.comp (Primrec.option_map (node.comp Primrec.fst)
    (rowPrim.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂) (Primrec.const 0)

theorem exact_OriginalRawNeutralRankPrimrec : Primrec rawRank := by
  have step : Primrec₂ (fun n (xs : List Nat) => xs ++ [next n xs]) :=
    Primrec.list_append.comp Primrec.snd (Primrec.list_cons.comp nextPrim (Primrec.const []))
  have tables : Primrec table := (Primrec.nat_rec₁ [] step).of_eq (fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [table,ih])
  exact nextPrim.comp Primrec.id tables

/-- One real numerical program for the original raw neutral-spine rank,
agreeing at malformed inputs as well as canonical inputs. -/
theorem exact_OriginalRawNeutralRankProgram :
    ∃ g : Program 1, ∀ n, evaluate g (n ::ᵥ nil) = rawRank n := by
  have f : Primrec (fun v : List.Vector Nat 1 => rawRank (v.get 0)) :=
    exact_OriginalRawNeutralRankPrimrec.comp (Primrec.vector_get.comp Primrec.id (Primrec.const 0))
  obtain ⟨g,fit⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 1 _ f
  exact ⟨g,fun n => fit (n ::ᵥ nil)⟩

#print axioms exact_OriginalRawNeutralRankPrimrec
#print axioms exact_OriginalRawNeutralRankProgram
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankProgramProof
