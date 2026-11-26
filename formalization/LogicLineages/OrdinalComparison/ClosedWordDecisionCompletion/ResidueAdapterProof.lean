module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueRowProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmItemProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ResidueAdapterProof
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LogicLineages.ModelsAlgebra.Forests

/-- Atom-local facts retain every occurrence, including zero coefficients. -/
theorem atom_allowed (D : Nat) (p : Formula) (a : Atom)
    (hp : Formula.allowed D p) (ha : a ∈ p.atoms) : RowAllowed D a.row := by
  intro b hb
  exact hp b.2 (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)

theorem atom_names (p : Formula) (a : Atom) (ha : a ∈ p.atoms) :
    NamesFrom p.variables a.row := by
  intro i hi
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hi
  exact List.mem_map.mpr ⟨b.2,List.mem_flatMap.mpr ⟨a,ha,
    List.mem_map.mpr ⟨b,hb,rfl⟩⟩,rfl⟩

theorem allowed_iff_rows (D : Nat) (p : Formula) :
    Formula.allowed D p ↔ ∀ a ∈ p.atoms, RowAllowed D a.row := by
  constructor
  · intro hp a ha
    exact atom_allowed D p a hp ha
  · intro hp t ht
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    exact hp a ha b hb

theorem meaningful_iff_rows (p : Formula) (ν : Nat → Nat) :
    Formula.meaningful p ν ↔ ∀ a ∈ p.atoms, RowDomain a.row ν := by
  constructor
  · intro hp a ha b hb
    exact hp b.2 (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
  · intro hp t ht
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ht
    exact hp a ha b hb

theorem variables_eq_rows (p : Formula) :
    p.variables = p.atoms.flatMap (fun a => rowVariables a.row) := by
  simp only [Formula.variables,Formula.tokens,List.map_flatMap,List.map_map,
    Function.comp_def,rowVariables]

theorem residue_atoms (p : Formula) :
    (residue p).atoms = p.atoms.map residueAtom := by
  induction p with
  | bot => rfl
  | top => rfl
  | atom a => rfl
  | neg p ih => exact ih
  | conj p q ihp ihq =>
      simp only [residue,CotreePresburgerUnit.Boolean.atoms,ihp,ihq,List.map_append]
  | disj p q ihp ihq =>
      simp only [residue,CotreePresburgerUnit.Boolean.atoms,ihp,ihq,List.map_append]

theorem residue_variables (p : Formula) :
    (residue p).variables = p.variables := by
  rw [variables_eq_rows,residue_atoms,variables_eq_rows]
  simp only [List.flatMap_map]
  apply congrArg (fun f : Atom → List Nat => p.atoms.flatMap f)
  funext a
  cases a with
  | nonnegative r => rfl
  | divisible m r => exact WordResidue.Proof.exactNames (m+1) r

theorem residue_allowed (D : Nat) (p : Formula) (hp : Formula.allowed D p) :
    Formula.allowed D (residue p) := by
  apply (allowed_iff_rows D _).mpr
  intro a ha
  rw [residue_atoms] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  cases b with
  | nonnegative r => exact atom_allowed D p (.nonnegative r) hp hb
  | divisible m r =>
      exact (WordResidue.Proof.outputDomainsAndDegree D (m+1) r (fun _ => 0)).2

theorem residue_congruences_linear (maximum : Nat) (p : Formula) :
    OutcomeTransport.CongruencesLinear maximum (residue p) := by
  intro mr hmr
  simp only [OutcomeTransport.congruences] at hmr
  obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp hmr
  rw [residue_atoms] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  cases b with
  | nonnegative r => simp [residueAtom] at he
  | divisible m r =>
      have hpair : (m,WordResidue.row (m+1) r) = mr := by
        simpa only [residueAtom,Option.some.injEq] using he
      subst mr
      intro a ha hname
      exact (WordResidue.Proof.literalRawSyntax (m+1) r).2 a ha

theorem exactResidueSyntax : BranchTargets.ExactResidueSyntax := by
  intro D p
  exact ⟨residue_variables p,residue_allowed D p,
    fun maximum => residue_congruences_linear maximum p⟩

/-- This bound refers to the old formula, before congruence words disappear. -/
theorem original_meaningful (D : Nat) (p : Formula) (ν : Nat → Nat)
    (hp : Formula.allowed D p)
    (hν : ∀ i ∈ p.variables, OutcomeTransport.originalTail p ≤ ν i) :
    Formula.meaningful p ν := by
  apply (meaningful_iff_rows p ν).mpr
  intro a ha
  have hb : Algorithm.rowTail a.row ≤ OutcomeTransport.originalTail p :=
    AlgorithmProof.member_le_foldMax _ _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  exact AlgorithmProof.rowTail_domain D a.row ν (atom_allowed D p a hp ha)
    (fun i hi => hb.trans (hν i (atom_names p a ha i hi)))

theorem residue_meaningful (p : Formula) (ν : Nat → Nat)
    (hp : Formula.meaningful p ν) : Formula.meaningful (residue p) ν := by
  apply (meaningful_iff_rows _ ν).mpr
  intro a ha
  rw [residue_atoms] at ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  cases b with
  | nonnegative r => exact (meaningful_iff_rows p ν).mp hp (.nonnegative r) hb
  | divisible m r => exact (WordResidue.Proof.outputDomainsAndDegree 0 (m+1) r ν).1

theorem residue_eval_of_atoms (p : Formula) (ν : Nat → Nat) :
    (∀ a ∈ p.atoms, (residueAtom a).eval ν ↔ a.eval ν) →
      (Formula.eval ν (residue p) ↔ Formula.eval ν p) := by
  induction p with
  | bot => intro _; rfl
  | top => intro _; rfl
  | atom a =>
      intro h
      exact h a (by simp [CotreePresburgerUnit.Boolean.atoms])
  | neg p ih =>
      intro h
      exact not_congr (ih h)
  | conj p q ihp ihq =>
      intro h
      exact and_congr
        (ihp (fun a ha => h a (List.mem_append_left _ ha)))
        (ihq (fun a ha => h a (List.mem_append_right _ ha)))
  | disj p q ihp ihq =>
      intro h
      exact or_congr
        (ihp (fun a ha => h a (List.mem_append_left _ ha)))
        (ihq (fun a ha => h a (List.mem_append_right _ ha)))

theorem exactResidueSemantics : BranchTargets.ExactResidueSemantics := by
  intro D p hp ν hν
  have hold : Formula.meaningful p ν := original_meaningful D p ν hp
    (fun i hi => (Nat.le_max_left _ _).trans (hν i hi))
  refine ⟨hold,residue_meaningful p ν hold,?_⟩
  apply residue_eval_of_atoms p ν
  intro a ha
  cases a with
  | nonnegative r => rfl
  | divisible m r =>
      have hb : WordResidue.rowTail (m+1) r ≤ residueTail p :=
        AlgorithmProof.member_le_foldMax _ _ (List.mem_map.mpr ⟨.divisible m r,ha,rfl⟩)
      have ht : ∀ i ∈ rowVariables r, WordResidue.rowTail (m+1) r ≤ ν i := by
        intro i hi
        exact hb.trans ((Nat.le_max_right _ _).trans
          (hν i (atom_names p (.divisible m r) ha i hi)))
      exact (WordResidue.Proof.actualDivisibility D m r
        (atom_allowed D p (.divisible m r) hp ha) ν ht).symm

#print axioms atom_allowed
#print axioms atom_names
#print axioms allowed_iff_rows
#print axioms meaningful_iff_rows
#print axioms variables_eq_rows
#print axioms residue_atoms
#print axioms residue_variables
#print axioms residue_allowed
#print axioms residue_congruences_linear
#print axioms exactResidueSyntax
#print axioms original_meaningful
#print axioms residue_meaningful
#print axioms residue_eval_of_atoms
#print axioms exactResidueSemantics

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.ResidueAdapterProof
