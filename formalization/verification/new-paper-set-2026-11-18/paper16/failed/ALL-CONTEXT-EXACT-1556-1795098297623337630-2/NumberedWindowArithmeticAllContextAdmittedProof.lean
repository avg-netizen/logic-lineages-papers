import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAddressProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathDecodeProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLeastClassChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowSimulationData
open NumberedWindowArithmeticTermCode NumberedWindowTypingBits NumberedWindowTypingBitsChecks
open NumberedWindowArithmeticLeastClass NumberedWindowArithmeticLeastClassChecks
open NumberedWindowArithmeticAllContextBits NumberedWindowArithmeticAllContextTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticClassAddressProof

theorem canonical : ExactCanonicalAddressBit := by
  intro S K a hk
  constructor
  · intro h
    cases hDec : decodeTerm a.least with
    | none => simp [canonicalBit,hDec] at h
    | some rep =>
      simp only [canonicalBit,hDec,Bool.and_eq_true,decide_eq_true_eq] at h
      let Q : WindowCarrier S K (finiteC a.context) a.result :=
        ⟨rep,(exact_FiniteWindowBit S K a.context a.result rep).mp h.1⟩
      exact ⟨classOf Q,Q,rfl,h.2⟩
  · rintro ⟨_,Q,_,hQ⟩
    obtain ⟨code,rep,hl,_,he,hw,hp,_,_⟩ :=
      exact_LeastCodeSpecification S K a.context a.result Q.val hk Q.property
    have hCode : code = a.least := Option.some.inj (hl.symm.trans hQ)
    have dRep : decodeTerm a.least = some rep :=
      NumberedWindowArithmeticPathDecodeProof.termAt (he.trans hCode)
    have eqCode := (exact_LeastCodeReflectsPrimary S K a.context a.result Q.val rep
      hk Q.property hw).mpr hp
    have hLeast : leastCode S K a.context a.result rep = some a.least :=
      eqCode.symm.trans hQ
    simp only [canonicalBit,dRep,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨(exact_FiniteWindowBit S K a.context a.result rep).mpr hw,hLeast⟩

theorem admitted : ExactAdmittedAddressBit := by
  intro S K n hk
  constructor
  · intro h
    cases ha : decodeAddress n with
    | none => simp [addressBit,ha] at h
    | some a =>
      rcases a with ⟨Γ,τ,least⟩
      have hOk : canonicalBit S K ⟨Γ,τ,least⟩ = true := by
        simpa only [addressBit,ha] using h
      obtain ⟨x,hx⟩ := (canonical S K ⟨Γ,τ,least⟩ hk).mp hOk
      exact ⟨Γ,τ,least,x,read ha,hx⟩
  · rintro ⟨Γ,τ,least,x,ha,hx⟩
    simpa only [addressBit,atCode ha] using (canonical S K ⟨Γ,τ,least⟩ hk).mpr ⟨x,hx⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
