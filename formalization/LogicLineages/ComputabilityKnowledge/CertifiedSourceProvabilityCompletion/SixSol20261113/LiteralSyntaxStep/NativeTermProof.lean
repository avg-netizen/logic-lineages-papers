module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeTermProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof NativeAtomsProof
attribute [local irreducible] evaluate
theorem token0 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 0 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 0) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token1 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 1 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 1) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token2 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 2 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 2) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token3 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 3 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 3) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token4 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 4 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 4) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem token5 (n : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ 5 ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) 5) := by
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,oneAt,twoAt,binderAt,GorbowSyntaxValidation.expand]
theorem other (n token : Nat) (h : 6 ≤ token) : evaluate termBranch (Nat.pair 0 n ::ᵥ token ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) token) := by
 have h0 : token ≠ 0 := by omega
 have h1 : token ≠ 1 := by omega
 have h2 : token ≠ 2 := by omega
 have h3 : token ≠ 3 := by omega
 have h4 : token ≠ 4 := by omega
 have h5 : token ≠ 5 := by omega
 simp [termBranch,whenEqualEval,projectionEval,get2_1,constantEval,GorbowSyntaxValidation.expand,h0,h1,h2,h3,h4,h5]
theorem branchAt (n token : Nat) : evaluate termBranch (Nat.pair 0 n ::ᵥ token ::ᵥ nil) =
 Encodable.encode (GorbowSyntaxValidation.expand (0,n) token) := by
 by_cases h0 : token=0
 · subst token; exact token0 n
 by_cases h1 : token=1
 · subst token; exact token1 n
 by_cases h2 : token=2
 · subst token; exact token2 n
 by_cases h3 : token=3
 · subst token; exact token3 n
 by_cases h4 : token=4
 · subst token; exact token4 n
 by_cases h5 : token=5
 · subst token; exact token5 n
 exact other n token (by omega)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeTermProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.NativeTermProof
