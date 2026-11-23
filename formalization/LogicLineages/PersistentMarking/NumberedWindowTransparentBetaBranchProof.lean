module
public import LogicLineages.PersistentMarking.NumberedWindowBinderRootAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowTransparentBetaBranchProof

open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowMarkRootAlgorithm (guarded)
open NumberedWindowBinderRootAlgorithm (beta betaRows)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

/-- The first physical output of the existing singleton-substitution algorithm
at depth zero, selected from exactly the fields read by the original beta row. -/
def instanceOutput (p fn : Nat × List Nat) : Option Nat :=
  (NumberedWindowSingletonAlgorithm.output (p.2.getD 3 0) 0 (fn.2.getD 1 0)).1

/-- Exact beta-row acceptance on all decoded pairs, including malformed
ones, with no promise of success from the substitution algorithm. -/
theorem row_iff (dst : Nat) (p fn : Nat × List Nat) :
    betaRows dst p fn = true ↔
      p.1 = 6 ∧ fn.1 = 2 ∧ p.2.getD 0 0 = fn.2.getD 0 0 ∧
        instanceOutput p fn = some dst := by
  unfold betaRows
  change ((p.1 == 6) && (fn.1 == 2) &&
    (p.2.getD 0 0 == fn.2.getD 0 0) &&
    (instanceOutput p fn).any (· == dst)) = true ↔ _
  cases h : instanceOutput p fn with
  | none => simp [h]
  | some out => simp [h, and_assoc]

/-- An actual result of substitution plus the original syntax and literal
field guards supplies acceptance on the original raw endpoints. In particular
this does not change either endpoint or infer the syntax conditions. -/
theorem acceptOriginal (src dst : Nat) (p fn : Nat × List Nat)
    (hsrc : (syntaxBits src).1 = true) (hdst : (syntaxBits dst).1 = true)
    (hp : unpackNode src = some p) (hf : unpackNode (p.2.getD 2 0) = some fn)
    (hpTag : p.1 = 6) (hfTag : fn.1 = 2)
    (hty : p.2.getD 0 0 = fn.2.getD 0 0)
    (hout : instanceOutput p fn = some dst) :
    beta src dst = true := by
  have hr : betaRows dst p fn = true := (row_iff dst p fn).mpr ⟨hpTag,hfTag,hty,hout⟩
  simp only [beta, guarded, hsrc, hdst, hp, hf, Option.any_some, hr, Bool.true_and]

#print axioms row_iff
#print axioms acceptOriginal
end LogicLineages.PersistentMarking.NumberedWindowTransparentBetaBranchProof
