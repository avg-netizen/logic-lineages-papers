module
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionTargets
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionProgramsProof
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Proof

theorem encodedWitness : Targets.EncodedWitness := by
  intro b code k
  unfold test
  cases h : Encodable.decode (α := List Nat) k <;> simp

theorem witness_exists (b code : Nat) :
    (∃ k, test b code k=true) ↔
    ∃ xs, SourceGammaCounterexample.counterexample b code xs=true := by
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨xs,_,hx⟩ := (encodedWitness b code k).mp hk
    exact ⟨xs,hx⟩
  · rintro ⟨xs,hx⟩
    exact ⟨Encodable.encode xs,(encodedWitness b code _).mpr ⟨xs,Encodable.encodek xs,hx⟩⟩

theorem exactSearch : Targets.ExactSearch := by
  intro b code
  constructor
  · change (Nat.rfind (fun k => Part.some (test b code k))).Dom ↔ _
    rw [Nat.rfind_dom]
    have h : (∃ n, true ∈ Part.some (test b code n) ∧
        ∀ {m : Nat}, m<n → (Part.some (test b code m)).Dom) ↔
        ∃ n, test b code n=true := by
      constructor
      · rintro ⟨n,hn,_⟩
        exact ⟨n,(Part.mem_some_iff.mp hn).symm⟩
      · rintro ⟨n,hn⟩
        exact ⟨n,Part.mem_some_iff.mpr hn.symm,fun {_} _ => Part.some_dom _⟩
    rw [h,witness_exists]
    exact (SourceGammaCounterexample.Proof.exactCounterexample b code).symm
  · intro k
    change k ∈ Nat.rfind (fun j => Part.some (test b code j)) ↔ _
    rw [Nat.mem_rfind]
    constructor
    · rintro ⟨hk,hj⟩
      exact ⟨(Part.mem_some_iff.mp hk).symm,fun j hjk => (Part.mem_some_iff.mp (hj hjk)).symm⟩
    · rintro ⟨hk,hj⟩
      exact ⟨Part.mem_some_iff.mpr hk.symm,fun {j} hjk => Part.mem_some_iff.mpr (hj j hjk).symm⟩

theorem fixedSemidecision : Targets.FixedSemidecision := by
  intro b
  refine ⟨testComputable b,searchPartrec b,?_⟩
  exact (searchPartrec b).dom_re.of_eq (fun code => (exactSearch b code).1)

theorem universalNormalForm : Targets.UniversalNormalForm := by
  intro b
  constructor
  · have h : Computable (fun p : Nat×Nat => decide (test b p.1 p.2=false)) :=
      (Primrec.eq.decide.to_comp.comp (testComputable b) (Computable.const false))
    exact h.computablePred
  · intro code
    have h := (SourceGammaCounterexample.Proof.exactCounterexample b code).trans
      (witness_exists b code).symm
    constructor
    · intro hm k
      cases hk : test b code k with
      | false => rfl
      | true => exact False.elim ((h.mpr ⟨k,hk⟩) hm)
    · intro hall
      by_contra hn
      obtain ⟨k,hk⟩ := h.mp hn
      have := hall k
      simp [hk] at this
end LogicLineages.OrdinalComparison.Source.SourceGammaSemidecision.Proof
