module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheoryTargets
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRNegativeNumeralsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowSourceRegistryPadding List.Vector
open GorbowPRChildTags GorbowTheoryProof
open GorbowPRDefiningEquations (call argumentVariables tailVariables equation nodeEquations)
open GorbowNamedRegistryInterpretation (interpretation)
open GorbowNamedRegistryInterpretation.Proof (internalTerm)

private theorem equationSound {ctx : Nat} (I : Interpretation) (lhs rhs : Term ctx)
    (h : ∀ rho, lhs.realize I rho = rhs.realize I rho) :
    (equation lhs rhs).realize I Fin.elim0 :=
  (GorbowStandardInductionProof.universalClosureSemantics ctx (.equal lhs rhs) I).mpr h

private theorem childLookup (pF pR : Program 1) (tag : Nat) {m : Nat} (q : Program m)
    (ht : (nodes (root pF pR))[tag]? = some ⟨m,q⟩) (localTag : Nat) (a : Packed)
    (hl : (nodes q)[localTag]? = some a) : (nodes (root pF pR))[tag+localTag]? = some a :=
  GorbowPRSubtree.Proof.lookupTransport 4 (root pF pR) tag ⟨m,q⟩ localTag a ht hl

private theorem nodeSound (pF pR : Program 1) (tag : Nat) (a : Packed)
    (ht : (nodes (root pF pR))[tag]? = some a) (I : Interpretation) (sigma : Sentence)
    (hs : sigma ∈ nodeEquations a.2 tag) :
    sigma.realize (interpretation pF pR I) Fin.elim0 := by
  obtain ⟨m,q⟩ := a
  cases q with
  | zero =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [internalTerm 0 pF pR tag 0 .zero List.Vector.nil I rho ht]
      rfl
  | succ =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [internalTerm 1 pF pR tag 1 .succ (argumentVariables 1) I rho ht]
      simp [evaluate, argumentVariables, Term.realize]
  | projection i =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      apply equationSound
      intro rho
      rw [internalTerm _ pF pR tag _ (.projection i) (argumentVariables _) I rho ht]
      simp [evaluate, argumentVariables, Term.realize]
  | @composition m k f g =>
      simp only [nodeEquations, List.mem_singleton] at hs
      subst sigma
      have hf := childLookup pF pR tag (.composition f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.compositionFunction m k f g)
      have hg : ∀ i, (nodes (root pF pR))[tag+argumentTag f g i]? = some ⟨m,g i⟩ :=
        fun i => childLookup pF pR tag (.composition f g) ht _ _
          (GorbowPRChildTags.Proof.compositionArgument m k f g i)
      apply equationSound
      intro rho
      rw [internalTerm m pF pR tag m (.composition f g) (argumentVariables m) I rho ht]
      rw [internalTerm m pF pR (tag+1) k f _ I rho hf]
      simp only [evaluate]
      apply congrArg (evaluate f)
      apply List.Vector.ext
      intro i
      simp only [List.Vector.get_ofFn, List.Vector.get_map]
      exact (internalTerm m pF pR _ m (g i) (argumentVariables m) I rho (hg i)).symm
  | @recursion k f g =>
      have hf := childLookup pF pR tag (.recursion f g) ht 1 ⟨k,f⟩
        (GorbowPRChildTags.Proof.recursionBase k f g)
      have hg := childLookup pF pR tag (.recursion f g) ht (stepTag f) ⟨k+2,g⟩
        (GorbowPRChildTags.Proof.recursionStep k f g)
      simp only [nodeEquations, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · apply equationSound
        intro rho
        rw [internalTerm k pF pR tag (k+1) (.recursion f g) _ I rho ht,
          internalTerm k pF pR (tag+1) k f _ I rho hf]
        simp [evaluate, Term.realize]
      · apply equationSound
        intro rho
        rw [internalTerm (k+1) pF pR tag (k+1) (.recursion f g) _ I rho ht,
          internalTerm (k+1) pF pR (tag+stepTag f) (k+2) g _ I rho hg]
        have hins := internalTerm (k+1) pF pR tag (k+1) (.recursion f g)
          (.var 0 ::ᵥ tailVariables k) I rho ht
        simp [evaluate, Term.realize, hins]


theorem internalEquationsSound : Targets.InternalEquationsSound := by
  intro pF pR I sigma hs
  have hall : ∀ entry ∈ (nodes (root pF pR)).zipIdx, ∀ sigma ∈ nodeEquations entry.1.2 entry.2,
      sigma.realize (interpretation pF pR I) Fin.elim0 := by
    refine (List.forall_mem_zipIdx' (l := nodes (root pF pR))
      (p := fun entry => ∀ sigma ∈ nodeEquations entry.1.2 entry.2,
        sigma.realize (interpretation pF pR I) Fin.elim0)).mpr ?_
    intro i hi sigma hs
    exact nodeSound pF pR i (nodes (root pF pR))[i] (by simp [hi]) I sigma hs
  obtain ⟨entry, he, hs⟩ := List.mem_flatMap.mp hs
  exact hall entry he sigma hs

private theorem functionAliasSound (pF pR : Program 1) (I : Interpretation)
    (name : Nat × Nat) (hn : name ∈ functionNames) :
    (functionAlias name).realize (interpretation pF pR I) Fin.elim0 := by
  apply equationSound
  intro rho
  let J := interpretation pF pR I
  let args := (argumentVariables name.1).toList.map (fun t => t.realize J rho)
  have hlen : args.length = name.1 := by simp [args]
  have hh : (headerVariables name).realize J rho =
      GorbowRegistryTuple.header name.1 name.2 args :=
    (GorbowRegistryTupleProof.termCalibration name.1 J rho).2.2 name.1 name.2 _
  have hi := internalTerm name.1 pF pR functionTag 1 pF
    (headerVariables name ::ᵥ List.Vector.nil) I rho
    (GorbowSourceRegistryPadding.Proof.functionRoot pF pR)
  calc
    (Term.universalFunction (headerVariables name)).realize J rho =
        GorbowNamedRegistryInterpretation.functionProgram pF pR
          (GorbowRegistryTuple.header name.1 name.2 args) :=
      congrArg (GorbowNamedRegistryInterpretation.functionProgram pF pR) hh
    _ = evaluate pF (GorbowRegistryTuple.header name.1 name.2 args ::ᵥ List.Vector.nil) :=
      GorbowNamedRegistryInterpretation.Proof.namedFunction pF pR name hn args hlen
    _ = (call functionTag (headerVariables name ::ᵥ List.Vector.nil)).realize J rho := by
      rw [hi]
      simp only [List.Vector.map_cons, List.Vector.map_nil]
      exact congrArg (fun x => evaluate pF (x ::ᵥ List.Vector.nil)) hh.symm

private theorem relationAliasSound (pF pR : Program 1) (I : Interpretation)
    (name : Nat × Nat) (hn : name ∈ relationNames) :
    (relationAlias pF name).realize (interpretation pF pR I) Fin.elim0 := by
  apply (GorbowStandardInductionProof.universalClosureSemantics _ _ _).mpr
  intro rho
  let J := interpretation pF pR I
  let args := (argumentVariables name.1).toList.map (fun t => t.realize J rho)
  have hlen : args.length = name.1 := by simp [args]
  have hh : (headerVariables name).realize J rho =
      GorbowRegistryTuple.header name.1 name.2 args :=
    (GorbowRegistryTupleProof.termCalibration name.1 J rho).2.2 name.1 name.2 _
  have hi := internalTerm name.1 pF pR (relationTag pF) 1 pR
    (headerVariables name ::ᵥ List.Vector.nil) I rho
    (GorbowSourceRegistryPadding.Proof.relationRoot pF pR)
  have hu : (Formula.universalRelation (headerVariables name)).realize J rho ↔
      GorbowNamedRegistryInterpretation.relationProgram pF pR
        (GorbowRegistryTuple.header name.1 name.2 args) = true := by
    change (GorbowNamedRegistryInterpretation.relationProgram pF pR
      ((headerVariables name).realize J rho) = true) ↔ _
    rw [hh]
  have he : (Formula.equal (call (relationTag pF) (headerVariables name ::ᵥ List.Vector.nil))
      (Term.numeral 1)).realize J rho ↔
      evaluate pR (GorbowRegistryTuple.header name.1 name.2 args ::ᵥ List.Vector.nil) = 1 := by
    change ((call (relationTag pF) (headerVariables name ::ᵥ List.Vector.nil)).realize J rho =
      (Term.numeral 1).realize J rho) ↔ _
    rw [hi, numeral_realize]
    simp only [List.Vector.map_cons, List.Vector.map_nil]
    exact Iff.of_eq (congrArg (fun x => evaluate pR (x ::ᵥ List.Vector.nil) = 1) hh)
  have heq := hu.trans ((GorbowNamedRegistryInterpretation.Proof.namedRelation pF pR name hn args hlen).trans he.symm)
  exact ⟨heq.mp,heq.mpr⟩

theorem aliasesSound : Targets.AliasesSound := by
  intro pF pR I sigma hs
  rcases List.mem_append.mp hs with hf | hr
  · obtain ⟨name,hn,rfl⟩ := List.mem_map.mp hf
    exact functionAliasSound pF pR I name hn
  · obtain ⟨name,hn,rfl⟩ := List.mem_map.mp hr
    exact relationAliasSound pF pR I name hn

theorem theorySoundness : Targets.TheorySoundness := by
  intro pF pR sigma proof I
  exact GorbowTheoryProofProof.theorySoundness (Theory pF pR) 0 sigma proof (interpretation pF pR I)
    (fun tau ht => (List.mem_append.mp ht).elim
      (internalEquationsSound pF pR I tau) (aliasesSound pF pR I tau)) Fin.elim0

theorem checkExact : Targets.CheckExact := by
  intro pF pR raw
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
  intro pF pR
  exact primitiveFiniteMembership _

theorem proofEmbedding : Targets.ProofEmbedding := by
  intro pF pR sigma h
  exact GorbowTheoryProofProof.monotonicity (GorbowPRNumeralCalculation.Theory (root pF pR))
    (Theory pF pR) (fun _ hs => List.mem_append_left _ hs) 0 sigma ⟨h⟩

theorem internalNumeralCertificates : Targets.InternalNumeralCertificates := by
  intro pF pR tag m q ht v
  constructor
  · obtain ⟨h⟩ := GorbowPRNumeralCalculation.Proof.numeralCalculation 4 (root pF pR) tag m q ht v
    exact proofEmbedding pF pR _ h
  · intro value hne
    obtain ⟨h⟩ := GorbowPRNegativeNumerals.Proof.negativeCalculation 4 (root pF pR) tag m q ht v value hne
    exact proofEmbedding pF pR _ h

theorem specificSourceModel : Targets.SpecificSourceModel := by
  obtain ⟨pF,pR,hf,hr⟩ := GorbowNamedRegistryInterpretation.Proof.specificNamedBridge
  exact ⟨pF,pR,hf,hr,theorySoundness pF pR⟩

end LogicLineages.ComputabilityKnowledge.GorbowNamedDefiningTheory.Proof
