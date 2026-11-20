import LogicLineages.PersistentMarking.NumberedWindowFreeAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessClassCode
import LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsProof

namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddressProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData NumberedWindowPrimary
open NumberedWindowFreeAddress NumberedWindowFreeAddressTargets
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode NumberedWindowArithmeticBinderCode
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticFieldAlgorithmChecks
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowPathWitnessTargets NumberedWindowPathWitnessClassCode
open NumberedWindowTypingBitsChecks NumberedWindowArithmeticTermCodeChecks
open NumberedWindowExternalTypeFactsChecks NumberedWindowPrimaryCoverSyntax
open NumberedWindowFieldAlgorithm (pack)

private def freeValue : NTerm → Option NTerm
  | .free σ name => some (.free σ name)
  | _ => none

private theorem preservesFree {S K C τ Q R} (h : Primary S K C τ Q R) :
    freeValue Q = freeValue R := by
  induction h using Primary.rec (motive_2 := fun _ _ _ _ _ => True) with
  | symm _ eq => exact eq.symm
  | trans _ _ left right => exact left.trans right
  | _ => first | rfl | trivial

private theorem freeUnchanged {S K C σ name R}
    (h : Primary S K C σ (.free σ name) R) : R = .free σ name := by
  have view : freeValue R = some (.free σ name) := (preservesFree h).symm
  cases R <;> simp_all [freeValue]

private theorem binders (Γ : List Ty) : pack (Γ.map encodeTy) = encodeBinders Γ := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih =>
      simp [pack,encodeBinders,ih,NumberedWindowActualPairAlgorithmChecks.currentPair]

theorem freeExact : ExactFreeAddress := by
  intro S K Γ hk σ hσ name
  let V : WindowCarrier S K (finiteC Γ) σ :=
    ⟨.free σ name,.free,hk σ hσ,by simp [heads]⟩
  obtain ⟨n,R,hLeast,_,hCode,_,hPrimary,_,_⟩ :=
    exact_LeastCodeSpecification S K Γ σ V.val hk V.property
  have same : R = .free σ name := freeUnchanged hPrimary
  have code : encodeTerm V.val = n := by simpa [V,same] using hCode
  have actual : ActualCodeAt S K Γ σ (encodeTerm V.val) (classOf V) :=
    ⟨V,rfl,code.symm ▸ hLeast⟩
  have address : freeAddress (Γ.map encodeTy) (encodeTy σ) name =
      encodeAddress ⟨Γ,σ,encodeTerm V.val⟩ := by
    change freeAddress (Γ.map encodeTy) (encodeTy σ) name =
      encodeAddress ⟨Γ,σ,encodeTerm (.free σ name)⟩
    simp only [freeAddress,encodeAddress,encodeTerm,exact_ExactTaggedNodeCodec.1,binders]
  refine ⟨V,rfl,address,actual,?_,?_⟩
  · rw [address,addressBit,round]
    exact (NumberedWindowArithmeticAllContextAdmittedProof.canonical
      S K ⟨Γ,σ,encodeTerm V.val⟩ hk).mpr ⟨classOf V,actual⟩
  · exact exact_VariableComputability S K Γ σ hk (classOf V) ⟨V,⟨name,Or.inl rfl⟩,rfl⟩

theorem freshExact : ExactFreshArrowProbe := by
  intro S K Γ hk σ τ q i hq
  have valid := (NumberedWindowArithmeticAllContextAdmittedProof.canonical
    S K ⟨Γ,.arrow σ τ,i⟩ hk).mpr ⟨q,hq⟩
  cases read : decodeTerm i with
  | none => simp [canonicalBit,read] at valid
  | some R =>
    simp only [canonicalBit,read,Bool.and_eq_true,decide_eq_true_eq] at valid
    let Q : WindowCarrier S K (finiteC Γ) (.arrow σ τ) :=
      ⟨R,(exact_FiniteWindowBit S K Γ (.arrow σ τ) R).mp valid.1⟩
    have sameClass : classOf Q = q :=
      NumberedWindowPathWitnessClassCode.sameClass hk ⟨Q,rfl,valid.2⟩ hq
    have original : encodeTerm Q.val = i := (exact_TermCodec.1 i R).mp read
    have name : freshName i = (termBounds Q.val).numeral + 1 := by
      rw [freshName,← original,NumberedWindowArithmeticCoverBoundsProof.term]
    have inside := NumberedWindowApplicationDomainProof.rootInWindow Q.property
    have domain : σ ∈ K := NumberedWindowApplicationDomainProof.arrowLeft hk inside σ
      (NumberedWindowApplicationDomainProof.subtypeSelf σ)
    exact ⟨Q,rfl,sameClass,name,freeExact S K Γ hk σ domain (freshName i)⟩

end LogicLineages.PersistentMarking.NumberedWindowFreeAddressProof
