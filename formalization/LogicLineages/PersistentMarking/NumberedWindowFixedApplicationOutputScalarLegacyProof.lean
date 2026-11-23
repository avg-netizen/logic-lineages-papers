import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextAdmittedProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarChecks

namespace LogicLineages.PersistentMarking.NumberedWindowFixedApplicationOutputScalarLegacyProof
open NumberedWindowSyntax NumberedWindowAddressApplication NumberedWindowAddressApplicationTargets
open NumberedWindowAddressApplicationChecks
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowScalarAlgorithm (scalar)
open NumberedWindowArithmeticScalarChecks (exact_ScalarAddress)
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticClassAddressProof (read)
open NumberedWindowArithmeticAllContextAdmittedProof (admitted canonical)

/-- The output carrier of the original numeric graph on a genuinely closed
source window. This uses the actual quotient application, not raw seed shape. -/
theorem exact_FixedApplicationOutputScalar (S : Spine.Signature) (K : List Ty)
    (closedK : DecisionSourceUniverse.Closed K) (f u y : Nat)
    (h : graph (fixed S K) f u y = true) : scalar (fixed S K) y = true := by
  have source : application (fixed S K) f u = some y := by
    exact eq_of_beq h
  have hApp : decodedApplication S K f u = some y :=
    (exact_DecodedApplication S K f u).symm.trans source
  cases fView : decodeAddress f with
  | none => simp [decodedApplication, fView] at hApp
  | some q =>
    cases uView : decodeAddress u with
    | none => simp [decodedApplication, fView, uView] at hApp
    | some a =>
      rcases q with ⟨Γ,ft,i⟩
      rcases a with ⟨Δ,argTy,j⟩
      cases ft with
      | ground => simp [decodedApplication, fView, uView] at hApp
      | arrow σ τ =>
        have ok :
            (canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ && canonicalBit S K ⟨Δ,argTy,j⟩ &&
              decide (Γ = Δ) && decide (σ = argTy)) = true := by
          by_cases good : (canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ && canonicalBit S K ⟨Δ,argTy,j⟩ &&
              decide (Γ = Δ) && decide (σ = argTy)) = true
          · exact good
          · simp only [decodedApplication, fView, uView, Option.bind_eq_bind, Option.bind_some,
              if_neg good] at hApp <;> cases hApp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
        obtain ⟨⟨⟨qGood,aGood⟩,contexts⟩,types⟩ := ok
        subst Δ
        subst argTy
        obtain ⟨q,hq⟩ := (canonical S K ⟨Γ,.arrow σ τ,i⟩ closedK).mp qGood
        obtain ⟨a,ha⟩ := (canonical S K ⟨Γ,σ,j⟩ closedK).mp aGood
        have goodApp : decodedApplication S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩)
            (encodeAddress ⟨Γ,σ,j⟩) = some y := by
          rw [read fView, read uView]
          exact hApp
        obtain ⟨k,hy,hk⟩ := (exact_ClassApplication S K Γ σ τ closedK q a i j hq ha y).mp goodApp
        exact (congrFun (exact_ScalarAddress S K) y).trans
          ((admitted S K y closedK).mpr ⟨Γ,τ,k,_,hy.symm,hk⟩)


#print axioms exact_FixedApplicationOutputScalar
end LogicLineages.PersistentMarking.NumberedWindowFixedApplicationOutputScalarLegacyProof
