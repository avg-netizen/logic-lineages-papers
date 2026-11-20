import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationCertificateProof
import LogicLineages.PersistentMarking.NumberedWindowOuterShapeChecks
import LogicLineages.PersistentMarking.NumberedWindowApplicationGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowExternalNeutralPrimaryProof
import LogicLineages.PersistentMarking.NumberedWindowPreservationGuardProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData NumberedWindowPrimary
open NumberedWindowNeutralApplicationAddress NumberedWindowNeutralApplicationAddressTargets
open NumberedWindowNeutralApplicationCertificateProof
open NumberedWindowOuterShape NumberedWindowOuterShapeTargets NumberedWindowOuterShapeChecks
open NumberedWindowAddressApplication NumberedWindowApplicationGraphChecks
open NumberedWindowAddressApplicationTargets NumberedWindowAddressApplicationChecks
open NumberedWindowDirectClassAddressTargets NumberedWindowClassPathWitnessBits
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticPathCodeChecks NumberedWindowRawWitnessBits NumberedWindowTypingBitsChecks
open NumberedWindowPathWitnessClassCode NumberedWindowPathWitnessTargets NumberedWindowExternalApplication
open NumberedWindowExternalNeutralTargets NumberedWindowExternalNeutralPrimaryProof
open NumberedWindowPreservationGuardProof (appParts)

private theorem decodedEdge {S : Signature} {K Γ : List Ty} {τ : Ty} {i target cert : Nat}
    (success : literalDirect S K (encodeAddress ⟨Γ,τ,i⟩) cert target = true) :
    ∃ (j : Nat) (e : ClassEdgeWitness),
      target = encodeAddress ⟨Γ,τ,j⟩ ∧ cert = encodeClassEdge e ∧
        classEdgeBit S K Γ τ i j e = true := by
  cases hd : decodeAddress target with
  | none => simp [literalDirect,round,hd] at success
  | some b =>
    rcases b with ⟨Δ,ρ,j⟩
    simp only [literalDirect,round,hd,Bool.and_eq_true,decide_eq_true_eq] at success
    have context : Γ = Δ := success.1.1
    have type : τ = ρ := success.1.2
    subst Δ
    subst ρ
    cases he : decodeClassEdge cert with
    | none => simp [classEdgeCodeBit,he] at success
    | some e =>
      exact ⟨j,e,(read hd).symm,((exact_ClassEdgeWitnessCodec.1 cert e).mp he).symm,
        by simpa only [classEdgeCodeBit,he] using success.2⟩

private theorem tagStable {S K C τ Q R} (h : Primary S K C τ Q R) :
    literalTag Q = literalTag R := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | symm _ eq => exact eq.symm
  | trans _ _ left right => exact left.trans right
  | _ => first | rfl | trivial

private theorem classifyArrow {S : Signature} {K Γ : List Ty} {σ τ : Ty}
    (hk : DecisionSourceUniverse.Closed K) {q : Class S K (finiteC Γ) (.arrow σ τ)}
    {i argument applied target cert : Nat}
    (hq : ActualCodeAt S K Γ (.arrow σ τ) i q) (hn : ClassNonLambda q)
    (graphSuccess : graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) argument applied = true)
    (edgeSuccess : literalDirect S K applied cert target = true) :
    outerShape (fixed S K) target = some 3 ∨
      ∃ next childCertificate,
        functionWitness (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) cert =
          some (next,childCertificate) ∧
        literalDirect S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩) childCertificate next = true ∧
        graph (fixed S K) next argument target = true := by
  obtain ⟨a,u,b,argCode,hu,appliedCode,ha⟩ :=
    (exact_ClassApplicationGraph S K Γ σ τ hk q i hq argument applied).mp graphSuccess
  rw [appliedCode] at edgeSuccess
  obtain ⟨j,e,targetCode,certCode,checked⟩ := decodedEdge edgeSuccess
  simp only [classEdgeBit,finiteWindowWitnessBit,Bool.and_eq_true,decide_eq_true_eq] at checked
  let B : WindowCarrier S K (finiteC Γ) τ :=
    ⟨e.source,(exact_FiniteWindowBit S K Γ τ e.source).mp checked.1.1.1.2⟩
  let W : WindowCarrier S K (finiteC Γ) τ :=
    ⟨e.target,(exact_FiniteWindowBit S K Γ τ e.target).mp checked.1.1.2⟩
  have codeB : ActualCodeAt S K Γ τ b (classOf B) := ⟨B,rfl,checked.1.2⟩
  have codeW : ActualCodeAt S K Γ τ j (classOf W) := ⟨W,rfl,checked.2⟩
  have classB := sameClass hk codeB ha
  have hqCopy := hq
  obtain ⟨F,classF,_⟩ := hqCopy
  obtain ⟨U,classU,leastU⟩ := hu
  have literalClass : classOf (appCarrier hk F U) = appClass hk q u := by
    rw [← classF,← classU]
    rfl
  have primaryB := primaryOfClassEquality (appCarrier hk F U) B (literalClass.trans classB.symm)
  obtain ⟨Q,A,shape,primaryQ,primaryA⟩ :=
    applicationComponents S K (finiteC Γ) σ τ F.val U.val B.val primaryB
  have beforeWindow : InWindow S K (finiteC Γ) τ (.auxApp σ τ Q A) := shape ▸ B.property
  let F₀ : WindowCarrier S K (finiteC Γ) (.arrow σ τ) := ⟨Q,(appParts beforeWindow).1⟩
  let U₀ : WindowCarrier S K (finiteC Γ) σ := ⟨A,(appParts beforeWindow).2⟩
  have sameFunction : classOf F₀ = q := calc
    classOf F₀ = classOf F := Quot.sound (.symm primaryQ)
    _ = q := classF
  have sameArgument : classOf U₀ = u := calc
    classOf U₀ = classOf U := Quot.sound (.symm primaryA)
    _ = u := classU
  have raw : rawBit S K e.witness (.auxApp σ τ Q A) e.target = true := by
    change B.val = .auxApp σ τ Q A at shape
    exact shape ▸ checked.1.1.1.1
  rcases suppliedCases (hn F₀ sameFunction) raw with bottom | ⟨R,child,witness,after,step⟩
  · apply Or.inl
    apply (exact_OuterShape S K hk target 3).mpr
    refine ⟨Γ,τ,j,classOf W,targetCode.symm,codeW,?_⟩
    intro P eq
    have tag := tagStable (primaryOfClassEquality P W eq)
    change literalTag P.val = literalTag e.target at tag
    simpa only [bottom,literalTag] using tag
  · apply Or.inr
    have afterWindow : InWindow S K (finiteC Γ) τ (.auxApp σ τ R A) := after ▸ W.property
    let R₀ : WindowCarrier S K (finiteC Γ) (.arrow σ τ) := ⟨R,(appParts afterWindow).1⟩
    have oldLeast : leastCode S K Γ (.arrow σ τ) Q = some i :=
      atRep hk F₀ sameFunction hq
    obtain ⟨k,_,leastR,_⟩ := exact_LeastCodeSpecification S K Γ (.arrow σ τ) R hk R₀.property
    have codeR : ActualCodeAt S K Γ (.arrow σ τ) k (classOf R₀) := ⟨R₀,rfl,leastR⟩
    have functionEdge : classEdgeBit S K Γ (.arrow σ τ) i k ⟨Q,R,child⟩ = true := by
      simp only [classEdgeBit,finiteWindowWitnessBit,Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨⟨⟨⟨step,(exact_FiniteWindowBit S K Γ (.arrow σ τ) Q).mpr F₀.property⟩,
        (exact_FiniteWindowBit S K Γ (.arrow σ τ) R).mpr R₀.property⟩,oldLeast⟩,leastR⟩
    have finalClass : classOf W = appClass hk (classOf R₀) u := by
      have literalW : W = appCarrier hk R₀ U₀ := Subtype.ext after
      rw [literalW,← sameArgument]
      rfl
    have valueAt : ActualCodeAt S K Γ τ j (appClass hk (classOf R₀) u) :=
      finalClass ▸ codeW
    have sameCertificate :
        e = ⟨.auxApp σ τ Q A,.auxApp σ τ R A,.auxFunction child⟩ := by
      cases e with
      | mk source target witnessCode =>
        change source = .auxApp σ τ Q A at shape
        change target = .auxApp σ τ R A at after
        change witnessCode = .auxFunction child at witness
        subst source
        subst target
        subst witnessCode
        rfl
    refine ⟨encodeAddress ⟨Γ,.arrow σ τ,k⟩,encodeClassEdge ⟨Q,R,child⟩,?_,?_,?_⟩
    · rw [certCode,sameCertificate]
      exact literal S K Γ σ τ i k Q R A child leastR
    · simp only [literalDirect,round,decide_true,Bool.true_and,
        classEdgeCodeBit,exact_ClassEdgeWitnessCodec.2.1]
      exact functionEdge
    · exact (exact_ClassApplicationGraph S K Γ σ τ hk (classOf R₀) k codeR argument target).mpr
        ⟨a,u,j,argCode,⟨U,classU,leastU⟩,targetCode,valueAt⟩

theorem classify : ExactNeutralApplicationAddress := by
  intro S K hk function argument applied target cert tag shape neutral app edge
  obtain ⟨Γ,ft,i,q,code,hq,tagAt⟩ := (exact_OuterShape S K hk function tag).mp shape
  rw [← code] at app ⊢
  cases ft with
  | ground =>
    have accepted : application (fixed S K) (encodeAddress ⟨Γ,.ground,i⟩) argument = some applied :=
      beq_iff_eq.mp app
    rw [exact_DecodedApplication S K] at accepted
    unfold decodedApplication at accepted
    rw [round] at accepted
    cases h : decodeAddress argument <;> simp [h] at accepted
  | arrow σ τ =>
    have hn : ClassNonLambda q := by
      intro R same ρ body lambda
      have tagEq := tagAt R same
      rw [lambda,literalTag] at tagEq
      exact neutral tagEq.symm
    exact classifyArrow hk hq hn app edge

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProof
