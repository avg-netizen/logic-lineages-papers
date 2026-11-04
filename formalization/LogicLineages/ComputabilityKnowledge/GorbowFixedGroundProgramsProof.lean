module

public import LogicLineages.ComputabilityKnowledge.GorbowFixedGroundProgramsTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoderProof

@[expose] public section
/-! Primitive recursion of FIXED programs and registries on all raw numeric
inputs. Every AST and registry list stays a fixed parameter outside the Primrec
function: a single program is checked by length and evaluated on a vector rebuilt
from its numeric list, a fixed finite registry is handled by external induction
over its entry list, and the decoded-header and named-overlay dispatchers are
assembled by option/if cases over the paid uniform header decoder. No uniform
evaluator over runtime ASTs, no full-ground identity and no source Base claim. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.Proof
open GorbowPRProgram GorbowPublishedDCB

/-! ### A single fixed program on numeric lists -/

private theorem ofFnGetD (args : List Nat) :
    List.ofFn (fun i : Fin args.length => args.getD i.val 0) = args := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

private theorem vectorOfList {n : Nat} (args : List Nat) (h : args.length = n) :
    List.Vector.ofFn (fun i : Fin n => args.getD i.val 0) = (⟨args, h⟩ : List.Vector Nat n) := by
  subst h
  apply List.Vector.eq
  rw [List.Vector.toList_ofFn, List.Vector.toList_mk]
  exact ofFnGetD args

private theorem pr_vector (n : Nat) :
    Primrec (fun args : List Nat => List.Vector.ofFn (fun i : Fin n => args.getD i.val 0)) :=
  Primrec.vector_ofFn (f := fun (i : Fin n) (args : List Nat) => args.getD i.val 0)
    (fun i => (Primrec.list_getD 0).comp Primrec.id (Primrec.const i.val))

private theorem checkedAgree {n : Nat} (p : Program n) (args : List Nat) :
    (if args.length = n then
        some (evaluate p (List.Vector.ofFn (fun i : Fin n => args.getD i.val 0)))
      else none) = checkedEvaluation p args := by
  unfold checkedEvaluation
  by_cases h : args.length = n
  · rw [if_pos h, dif_pos h, vectorOfList args h]
  · rw [if_neg h, dif_neg h]

theorem singleProgram : GorbowFixedGroundPrograms.Targets.SingleProgram := by
  intro n p
  have hc : PrimrecPred (fun args : List Nat => args.length = n) :=
    Primrec.eq.comp Primrec.list_length (Primrec.const n)
  have hv : Primrec (fun args : List Nat =>
      some (evaluate p (List.Vector.ofFn (fun i : Fin n => args.getD i.val 0)))) :=
    Primrec.option_some.comp ((GorbowPRProgram.Proof.primitiveEvaluation n p).comp (pr_vector n))
  have h := Primrec.ite hc hv (Primrec.const (none : Option Nat))
  exact h.of_eq (fun args => checkedAgree p args)

/-! ### A fixed finite registry, by external induction on its entries -/

private theorem pr_entries (L : List GorbowPRRegistry.Packed) :
    Primrec (fun x : Nat × List Nat => (L[x.1]?).bind (fun e => checkedEvaluation e.2 x.2)) := by
  induction L with
  | nil => exact (Primrec.const none).of_eq (fun x => by simp)
  | cons e rest ih =>
    have hz : PrimrecPred (fun x : Nat × List Nat => x.1 = 0) :=
      Primrec.eq.comp Primrec.fst (Primrec.const 0)
    have h := Primrec.ite hz ((singleProgram e.1 e.2).comp Primrec.snd)
      (ih.comp ((Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).pair Primrec.snd))
    refine h.of_eq (fun x => ?_)
    rcases x with ⟨tag, args⟩
    cases tag with
    | zero => simp
    | succ t => simp

theorem fixedRegistry : GorbowFixedGroundPrograms.Targets.FixedRegistry := by
  intro n p
  exact (pr_entries (GorbowPRRegistry.nodes p)).of_eq (fun x => rfl)

/-! ### The decoded-header defining dispatcher -/

private abbrev RawHeader := Nat × Nat × List Nat

private theorem pr_definingBody {n : Nat} (p : Program n) :
    Primrec (fun x : Nat × RawHeader =>
      if x.2.1 = x.2.2.2.length then (GorbowPRRegistry.dispatch p x.2.2.1 x.2.2.2).getD 0
      else 0) := by
  have hd : Primrec (fun x : Nat × RawHeader => GorbowPRRegistry.dispatch p x.2.2.1 x.2.2.2) :=
    (fixedRegistry n p).comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : PrimrecPred (fun x : Nat × RawHeader => x.2.1 = x.2.2.2.length) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.ite hc (Primrec.option_getD.comp hd (Primrec.const 0)) (Primrec.const 0)

theorem definingDispatcher : GorbowFixedGroundPrograms.Targets.DefiningDispatcher := by
  intro n p
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
    (Primrec.const 0) (pr_definingBody p).to₂
  exact h.of_eq (fun code => by
    cases hd : GorbowRegistryDecoder.decodeHeader code with
    | none => simp [GorbowPRDefiningEquations.functionProgram, hd]
    | some val =>
      obtain ⟨arity, tag, args⟩ := val
      simp [GorbowPRDefiningEquations.functionProgram, hd])

/-! ### The actual named overlay -/

private theorem memPred (L : List (Nat × Nat)) : PrimrecPred (fun x : Nat × Nat => x ∈ L) :=
  ((PrimrecRel.exists_mem_list (Primrec.eq : PrimrecRel (@Eq (Nat × Nat)))).comp
    (Primrec.const L) Primrec.id).of_eq (fun x => by simp)

private theorem namePred (L : List (Nat × Nat)) :
    PrimrecPred (fun x : Nat × RawHeader => (x.2.1, x.2.2.1) ∈ L ∧ x.2.2.2.length = x.2.1) :=
  ((memPred L).comp ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).and
    (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.fst.comp Primrec.snd))

private theorem pr_namedFunctionBody (pF pR : Program 1) :
    Primrec (fun x : Nat × RawHeader =>
      if (x.2.1, x.2.2.1) ∈ GorbowSourceRegistryPadding.functionNames ∧
          x.2.2.2.length = x.2.1 then
        (GorbowPRRegistry.dispatch (GorbowSourceRegistryPadding.root pF pR)
          GorbowSourceRegistryPadding.functionTag [x.1]).getD 0
      else GorbowPRDefiningEquations.functionProgram (GorbowSourceRegistryPadding.root pF pR) x.1) := by
  have hd : Primrec (fun x : Nat × RawHeader =>
      GorbowPRRegistry.dispatch (GorbowSourceRegistryPadding.root pF pR)
        GorbowSourceRegistryPadding.functionTag [x.1]) :=
    (fixedRegistry 4 (GorbowSourceRegistryPadding.root pF pR)).comp
      ((Primrec.const GorbowSourceRegistryPadding.functionTag).pair
        (Primrec.list_cons.comp Primrec.fst (Primrec.const [])))
  exact Primrec.ite (namePred GorbowSourceRegistryPadding.functionNames)
    (Primrec.option_getD.comp hd (Primrec.const 0))
    ((definingDispatcher 4 (GorbowSourceRegistryPadding.root pF pR)).comp Primrec.fst)

private theorem pr_namedFunction (pF pR : Program 1) :
    Primrec (GorbowNamedRegistryInterpretation.functionProgram pF pR) := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
    (Primrec.const 0) (pr_namedFunctionBody pF pR).to₂
  exact h.of_eq (fun code => by
    cases hd : GorbowRegistryDecoder.decodeHeader code with
    | none => simp [GorbowNamedRegistryInterpretation.functionProgram, hd]
    | some val =>
      obtain ⟨arity, tag, args⟩ := val
      simp [GorbowNamedRegistryInterpretation.functionProgram, hd])

private theorem pr_namedRelationBody (pF pR : Program 1) :
    Primrec (fun x : Nat × RawHeader =>
      if (x.2.1, x.2.2.1) ∈ GorbowSourceRegistryPadding.relationNames ∧
          x.2.2.2.length = x.2.1 then
        decide (GorbowPRRegistry.dispatch (GorbowSourceRegistryPadding.root pF pR)
          (GorbowSourceRegistryPadding.relationTag pF) [x.1] = some 1)
      else false) := by
  have hd : Primrec (fun x : Nat × RawHeader =>
      GorbowPRRegistry.dispatch (GorbowSourceRegistryPadding.root pF pR)
        (GorbowSourceRegistryPadding.relationTag pF) [x.1]) :=
    (fixedRegistry 4 (GorbowSourceRegistryPadding.root pF pR)).comp
      ((Primrec.const (GorbowSourceRegistryPadding.relationTag pF)).pair
        (Primrec.list_cons.comp Primrec.fst (Primrec.const [])))
  have he : PrimrecPred (fun x : Nat × RawHeader =>
      GorbowPRRegistry.dispatch (GorbowSourceRegistryPadding.root pF pR)
        (GorbowSourceRegistryPadding.relationTag pF) [x.1] = some 1) :=
    Primrec.eq.comp hd (Primrec.const (some 1))
  exact Primrec.ite (namePred GorbowSourceRegistryPadding.relationNames) he.decide
    (Primrec.const false)

private theorem pr_namedRelation (pF pR : Program 1) :
    Primrec (GorbowNamedRegistryInterpretation.relationProgram pF pR) := by
  have h := Primrec.option_casesOn GorbowRegistryDecoderProof.uniformPrograms.2.2.2.2
    (Primrec.const false) (pr_namedRelationBody pF pR).to₂
  exact h.of_eq (fun code => by
    cases hd : GorbowRegistryDecoder.decodeHeader code with
    | none => simp [GorbowNamedRegistryInterpretation.relationProgram, hd]
    | some val =>
      obtain ⟨arity, tag, args⟩ := val
      simp [GorbowNamedRegistryInterpretation.relationProgram, hd])

theorem namedOverlay : GorbowFixedGroundPrograms.Targets.NamedOverlay :=
  fun pF pR => ⟨pr_namedFunction pF pR, pr_namedRelation pF pR⟩

/-! ### Fixed unary ASTs for the actual ground fields -/

theorem actualPrograms : GorbowFixedGroundPrograms.Targets.ActualPrograms := by
  intro pF pR q c _
  obtain ⟨u, hu⟩ := (GorbowPRProgram.Proof.unaryCorrespondence
    (GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR)).mp
    (namedOverlay (augmented pF q) pR).1
  have hr : Primrec (fun x : Nat =>
      if GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR x then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (namedOverlay (augmented pF q) pR).2 (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)
  obtain ⟨r, hr'⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp hr
  exact ⟨u, r, fun x => ⟨hu x, hr' x⟩⟩

theorem fullTarget : GorbowFixedGroundPrograms.Targets.Target :=
  ⟨singleProgram, fixedRegistry, definingDispatcher, namedOverlay, actualPrograms⟩

end LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms.Proof
