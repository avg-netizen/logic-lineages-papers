module

public import LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquationsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRRegistryProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRChildTagsProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRSubtreeProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryTupleProof
public import LogicLineages.ComputabilityKnowledge.GorbowStandardInductionProof
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProofProof
public import Mathlib.Data.List.Enum

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags List.Vector

theorem headerCalibration : Targets.HeaderCalibration := by
  intro n p tag m q args h ht
  have hd := (GorbowRegistryDecoderProof.headerExact
    (GorbowRegistryTuple.header m tag args) m tag args).mpr rfl
  have hc := GorbowPRRegistry.Proof.exactDispatch n p tag m q args h ht
  simp [functionProgram, hd, h, hc]

theorem termCalibration : Targets.TermCalibration := by
  intro ctx n p tag m q args I rho ht
  let J := interpretation p I
  have hh := (GorbowRegistryTupleProof.termCalibration ctx J rho).2.2 m tag args.toList
  have hlen : (args.toList.map fun t => t.realize J rho).length = m := by simp
  have hc := headerCalibration n p tag m q
    (args.toList.map fun t => t.realize J rho) hlen ht
  exact (congrArg (functionProgram p) hh).trans hc

private theorem equationSound {ctx : Nat} (I : Interpretation) (lhs rhs : Term ctx)
    (h : ∀ rho, lhs.realize I rho = rhs.realize I rho) :
    (equation lhs rhs).realize I Fin.elim0 :=
  (GorbowStandardInductionProof.universalClosureSemantics ctx (.equal lhs rhs) I).mpr h

private theorem childLookup {n : Nat} (p : Program n) (tag : Nat) {m : Nat} (q : Program m)
    (ht : (nodes p)[tag]? = some ⟨m,q⟩) (localTag : Nat) (a : Packed)
    (hl : (nodes q)[localTag]? = some a) : (nodes p)[tag+localTag]? = some a :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨m,q⟩ localTag a ht hl

theorem nodeEquationsSound : Targets.NodeEquationsSound := by
  intro n p tag a ht I sigma hs
  obtain ⟨m,q⟩ := a
  cases q with
  | zero =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [termCalibration 0 n p tag 0 .zero List.Vector.nil I rho ht]
      rfl
  | succ =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [termCalibration 1 n p tag 1 .succ (argumentVariables 1) I rho ht]
      simp [evaluate, argumentVariables, Term.realize]
  | projection i =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [termCalibration _ n p tag _ (.projection i) (argumentVariables _) I rho ht]
      simp [evaluate, argumentVariables, Term.realize]
  | @composition m k f g =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      have hf := childLookup p tag (.composition f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.compositionFunction m k f g)
      have hg : ∀ i, (nodes p)[tag+argumentTag f g i]? = some ⟨m,g i⟩ :=
        fun i => childLookup p tag (.composition f g) ht _ _
          (GorbowPRChildTags.Proof.compositionArgument m k f g i)
      apply equationSound
      intro rho
      rw [termCalibration m n p tag m (.composition f g) (argumentVariables m) I rho ht]
      rw [termCalibration m n p (tag+1) k f _ I rho hf]
      simp only [evaluate]
      apply congrArg (evaluate f)
      apply List.Vector.ext
      intro i
      simp only [List.Vector.get_ofFn, List.Vector.get_map]
      exact (termCalibration m n p _ m (g i) (argumentVariables m) I rho (hg i)).symm
  | @recursion k f g =>
      have hf := childLookup p tag (.recursion f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.recursionBase k f g)
      have hg := childLookup p tag (.recursion f g) ht (stepTag f) ⟨k+2,g⟩
        (GorbowPRChildTags.Proof.recursionStep k f g)
      simp only [nodeEquations, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · apply equationSound
        intro rho
        rw [termCalibration k n p tag (k+1) (.recursion f g) _ I rho ht,
          termCalibration k n p (tag+1) k f _ I rho hf]
        simp [evaluate, Term.realize]
      · apply equationSound
        intro rho
        rw [termCalibration (k+1) n p tag (k+1) (.recursion f g) _ I rho ht,
          termCalibration (k+1) n p (tag+stepTag f) (k+2) g _ I rho hg]
        have hins := termCalibration (k+1) n p tag (k+1) (.recursion f g)
          (.var 0 ::ᵥ tailVariables k) I rho ht
        simp [evaluate, Term.realize, hins]

theorem allAxiomsSound : Targets.AllAxiomsSound := by
  intro n p I sigma hs
  have hall : ∀ entry ∈ (nodes p).zipIdx, ∀ sigma ∈ nodeEquations entry.1.2 entry.2,
      sigma.realize (interpretation p I) Fin.elim0 := by
    refine (List.forall_mem_zipIdx' (l := nodes p)
      (p := fun entry => ∀ sigma ∈ nodeEquations entry.1.2 entry.2,
        sigma.realize (interpretation p I) Fin.elim0)).mpr ?_
    intro i hi sigma hs
    exact nodeEquationsSound n p i (nodes p)[i] (by simp [hi]) I sigma hs
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  exact hall entry he sigma hs

theorem checkExact : Targets.CheckExact := by
  intro n p raw
  simp [check, List.mem_map]

private theorem primitiveFiniteMembership (codes : List (List Nat)) :
    Primrec (fun raw : List Nat => decide (raw ∈ codes)) := by
  induction codes with
  | nil => simpa using (Primrec.const false : Primrec (fun _ : List Nat => false))
  | cons code codes ih =>
      have hd := Primrec.or.comp (Primrec.eq.comp (Primrec.id : Primrec (fun x : List Nat => x))
        (Primrec.const code)).decide ih
      exact hd.of_eq (fun raw => by simp; rfl)

theorem fixedCheckerPrimitive : Targets.FixedCheckerPrimitive := by
  intro n p
  exact primitiveFiniteMembership _

theorem theorySoundness : Targets.TheorySoundness := by
  intro n p sigma proof I
  exact GorbowTheoryProofProof.theorySoundness (fun tau => tau ∈ axioms p) 0 sigma proof
    (interpretation p I) (fun tau ht => allAxiomsSound n p I tau ht) Fin.elim0

end LogicLineages.ComputabilityKnowledge.GorbowPRDefiningEquations.Proof
