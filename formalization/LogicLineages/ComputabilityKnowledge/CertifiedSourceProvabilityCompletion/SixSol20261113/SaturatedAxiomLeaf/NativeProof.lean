module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.NativeProof
open GorbowPRProgram GorbowProofChecker List.Vector
open SixSol20261112 HistoryDispatcher

/-- External semantic monotonicity, never used as an internal derivation. -/
theorem axiomMonotone (index s t line : Nat) (hst : s ≤ t)
 (h : axiomFunction (index ::ᵥ s ::ᵥ line ::ᵥ nil) = 1) :
 axiomFunction (index ::ᵥ t ::ᵥ line ::ᵥ nil) = 1 := by
 let l := decodedLine line
 have ha : GorbowTheoryChecker.axiomCheck
   (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,s))
   (context l) (conclusion l) (payload l) = true := by
  change truth (GorbowTheoryChecker.axiomCheck _ (context l) (conclusion l) (payload l)) = 1 at h
  unfold truth at h
  split at h
  · assumption
  · contradiction
 have hb : GorbowTheoryChecker.axiomCheck
   (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,t))
   (context l) (conclusion l) (payload l) = true := by
  simp only [GorbowTheoryChecker.axiomCheck,decide_eq_true_eq] at ha ⊢
  rcases ha with ⟨h0,h1,h2,h3,hv,ha,hs⟩
  refine ⟨h0,h1,h2,h3,hv,?_,hs⟩
  simp only [GorbowEnumeratedProvability.axiomCheck,decide_eq_true_eq] at ha ⊢
  exact Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hst (Option.mem_def.mpr ha))
 change truth (GorbowTheoryChecker.axiomCheck (GorbowEnumeratedProvability.axiomCheck (Denumerable.ofNat GorbowEnumeratedProvability.Code index,t)) (context l) (conclusion l) (payload l)) = 1
 rw [hb]
 rfl

theorem liftedValue (x : Program 3) (index fuel context formula line : Nat) :
 evaluate (lifted x) (Fuel.inputs index fuel context formula line) =
 evaluate x (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) := by
 change evaluate x (List.Vector.ofFn fun i => evaluate (liftArguments i) (Fuel.inputs index fuel context formula line)) = _
 congr 1

theorem saturatedValue (x : Program 3) (index fuel line : Nat) :
 evaluate (saturated x) (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) =
 evaluate (Fuel.verifier (lifted x)) (Fuel.inputs index fuel 0 0 line) := by
 change evaluate (Fuel.verifier (lifted x)) (List.Vector.ofFn fun i => evaluate (wrapperArguments i) (index ::ᵥ fuel ::ᵥ line ::ᵥ nil)) = _
 congr 1

theorem nativeCalibration : Targets.NativeCalibration := by
 intro x hx v
 obtain ⟨index,rest,rfl⟩ := List.Vector.exists_eq_cons v
 obtain ⟨fuel,rest,rfl⟩ := List.Vector.exists_eq_cons rest
 obtain ⟨line,rest,rfl⟩ := List.Vector.exists_eq_cons rest
 have hr : rest = nil := List.Vector.eq_nil rest
 subst rest
 rw [saturatedValue]
 have hspec := Fuel.NativeProof.nativeSaturation (lifted x) index fuel 0 0 line
 have hcal (k : Nat) : evaluate (lifted x) (Fuel.inputs index k 0 0 line) = axiomFunction (index ::ᵥ k ::ᵥ line ::ᵥ nil) := by
  rw [liftedValue,hx]
 by_cases h : axiomFunction (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) = 1
 · exact (hspec.1.mpr ⟨fuel,le_rfl,(hcal fuel).trans h⟩).trans h.symm
 · have hn : evaluate (Fuel.verifier (lifted x)) (Fuel.inputs index fuel 0 0 line) ≠ 1 := by
    intro he
    obtain ⟨k,hk,hv⟩ := hspec.1.mp he
    exact h (axiomMonotone index k fuel line hk ((hcal k).symm.trans hv))
   have hz := hspec.2.resolve_right hn
   rw [hz]
   have hb : axiomFunction (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) = 0 ∨ axiomFunction (index ::ᵥ fuel ::ᵥ line ::ᵥ nil) = 1 := by
    have truthRange (b : Bool) : truth b = 0 ∨ truth b = 1 := by
     cases b <;> simp [truth]
    exact truthRange _
   exact (hb.resolve_right h).symm
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.NativeProof
