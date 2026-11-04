module
public import LogicLineages.OrdinalComparison.SourceGammaCounterexampleProof
public import LogicLineages.OrdinalComparison.SourceGammaWeakCounterexampleProgramsProof
public import LogicLineages.OrdinalComparison.SourceRestrictedSyntaxCheckerProof
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorProof
public import LogicLineages.OrdinalComparison.SourceGammaCodedReductionAdequacyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Proof
open SourceGroundComponentEnvironment ParametricSourceEraser

theorem member_at_decode (G : Nat → Nat) (code n : Nat)
    (left right : OriginalTerm (List.replicate n Ty.ground) .ground)
    (hc : SourceMachineQueryCode.unpack code=some (n,SyntaxCode.encodeTerm left,SyntaxCode.encodeTerm right)) :
    SourceGammaWeakCodedReduction.RawMember G code ↔ SourceGammaWeakCodedReduction.Weak G left right := by
  constructor
  · rintro ⟨m,a,b,hd,hs⟩
    have he := Option.some.inj (hc.symm.trans hd)
    have hn : n=m := congrArg Prod.fst he
    subst m
    have hl := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.1) he)
    have hr := SourceTypedCodeAdequacy.Proof.typedCodeInjective (List.replicate n Ty.ground) Ty.ground
      (congrArg (fun p : SourceMachineQueryCode.Query => p.2.2) he)
    cases hl
    cases hr
    exact hs
  · exact fun h => ⟨n,left,right,hc,h⟩

theorem exactCounterexample : Targets.ExactCounterexample := by
  classical
  intro b code
  by_cases hsyntax : SourceGammaRestrictedReduction.RestrictedSyntax code
  · have hcheck := (SourceRestrictedSyntaxChecker.Proof.exactSyntaxClass code).mpr hsyntax
    obtain ⟨n,left,right,hc,hleft,hright,_,_⟩ := hsyntax
    have hsyntax' : SourceGammaRestrictedReduction.RestrictedSyntax code :=
      (SourceRestrictedSyntaxChecker.Proof.exactSyntaxClass code).mp hcheck
    constructor
    · intro hnot
      have hs : ¬SourceGammaWeakCodedReduction.Weak (SourceMachineControlNonperiodicity.gamma b) left right :=
        fun h => hnot ⟨hsyntax',(member_at_decode _ code n left right hc).mpr h⟩
      change ¬∀ ν : OrdinalComponent (List.replicate n Ty.ground) → Nat,
        (∀ c,0<ν c) → ∃ x y : Nat,
          Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (ν c : Ordinal)) left x ∧
          Scalar (SourceMachineControlNonperiodicity.gamma b) (fun c => (ν c : Ordinal)) right y ∧ x ≤ y at hs
      obtain ⟨ν,hν⟩ := not_forall.mp hs
      obtain ⟨hp,hfail⟩ := Classical.not_imp.mp hν
      obtain ⟨xs,hlen,hpos,hlookup⟩ := SourceGammaCounterexample.Proof.positiveCoverage.2 n ν hp
      have hval : rawValuation xs=ν := funext hlookup
      have hl := SourceGammaCounterexample.Proof.gamma_calibration b n left hleft xs hlen
      have hr := SourceGammaCounterexample.Proof.gamma_calibration b n right hright xs hlen
      obtain ⟨l,hel⟩ := hl.1
      obtain ⟨r,her⟩ := hr.1
      have hsl := (hl.2 l).mp hel
      have hsr := (hr.2 r).mp her
      rw [hval] at hsl hsr
      have hle : r<l := Nat.lt_of_not_ge (fun hlt => hfail ⟨l,r,hsl,hsr,hlt⟩)
      exact ⟨xs,by simp [counterexample,hcheck,hc,hlen,positive,hpos,hel,her,compareResults,hle]⟩
    · rintro ⟨xs,hw⟩ hmem
      have hguard : xs.length=n ∧ positive xs=true := by
        by_contra hn
        simp [counterexample,hcheck,hc,hn] at hw
      have hl := SourceGammaCounterexample.Proof.gamma_calibration b n left hleft xs hguard.1
      have hr := SourceGammaCounterexample.Proof.gamma_calibration b n right hright xs hguard.1
      obtain ⟨l,hel⟩ := hl.1
      obtain ⟨r,her⟩ := hr.1
      have hle : r<l := by
        simpa [counterexample,hcheck,hc,hguard,hel,her,compareResults] using hw
      have hstrict := (member_at_decode _ code n left right hc).mp hmem.2
      obtain ⟨x,y,hx,hy,hxy⟩ := hstrict (rawValuation xs) (SourceGammaCounterexample.Proof.positiveCoverage.1 n xs hguard.1 hguard.2)
      have hxl := ParametricSourceEraser.Proof.scalar_unique _ _ _ _ _ hx ((hl.2 l).mp hel)
      have hyr := ParametricSourceEraser.Proof.scalar_unique _ _ _ _ _ hy ((hr.2 r).mp her)
      omega
  · have hcheck : SourceRestrictedSyntaxChecker.restrictedCode code=false := by
      cases h : SourceRestrictedSyntaxChecker.restrictedCode code with
      | false => rfl
      | true => exact False.elim (hsyntax ((SourceRestrictedSyntaxChecker.Proof.exactSyntaxClass code).mp h))
    exact ⟨fun _ => ⟨[],explicitFailures.1 b code [] hcheck⟩,fun _ h => hsyntax h.1⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCounterexample.Proof
