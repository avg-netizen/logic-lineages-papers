module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage

open LogicLineages.OrdinalComparison.Source RawSourceDAG

private abbrev Task := List Nat × List Nat × Nat

private def rawChildren (s : Task) : List Task :=
  let d := s.2.2 / 8
  if s.2.2 % 8 = 5 then [(s.1,s.2.1,d.unpair.1),(s.1,s.2.1,d.unpair.2)]
  else if s.2.2 % 8 = 6 then [(s.1,d.unpair.1 :: s.2.1,d.unpair.2)]
  else []

private def rawAssemble (s : Task) (rs : List (List Node)) : List Node :=
  let (Γ,Δ,n) := s
  let d := n / 8
  let tag := n % 8
  let τ := (SyntaxCode.check (Δ++Γ) n).getD 0
  let node (k : Nat) (args : List Nat) : Node := (Δ,τ,k,args)
  let first := rs.getD 0 []
  let second := rs.getD 1 []
  if tag = 0 then [node 0 [d]]
  else if tag = 1 then [node 3 []]
  else if tag = 2 then [node 4 []]
  else if tag = 3 then [node 5 [d]]
  else if tag = 4 then [node 6 [d]]
  else if tag = 5 then
    let σ := (SyntaxCode.check (Δ++Γ) d.unpair.2).getD 0
    node 1 [σ,second.length,0] :: (second ++ first)
  else if tag = 6 then
    let β := (SyntaxCode.check ((d.unpair.1::Δ)++Γ) d.unpair.2).getD 0
    node 2 [d.unpair.1,β,0] :: first
  else []

private def measure (s : Task) : Nat := s.2.2

private theorem rawChildrenPrimitive : Primrec rawChildren := by
  have g : Primrec (fun x : Task => x.1) := Primrec.fst
  have d : Primrec (fun x : Task => x.2.1) := Primrec.fst.comp Primrec.snd
  have n : Primrec (fun x : Task => x.2.2) := Primrec.snd.comp Primrec.snd
  have payload := Primrec.nat_div.comp n (Primrec.const 8)
  have pr := Primrec.unpair.comp payload
  have l := Primrec.fst.comp pr
  have r := Primrec.snd.comp pr
  have tag := Primrec.nat_mod.comp n (Primrec.const 8)
  have test (k : Nat) : PrimrecPred (fun x : Task => x.2.2 % 8 = k) :=
    Primrec.eq.comp tag (Primrec.const k)
  have s₁ := g.pair (d.pair l)
  have s₂ := g.pair (d.pair r)
  have s₃ := g.pair ((Primrec.list_cons.comp l d).pair r)
  have single {a : Task → Task} (h : Primrec a) : Primrec (fun x => [a x]) :=
    Primrec.list_cons.comp h (Primrec.const [])
  exact Primrec.ite (test 5) (Primrec.list_cons.comp s₁ (single s₂))
    (Primrec.ite (test 6) (single s₃) (Primrec.const []))

private theorem rawAssemblePrimitive : Primrec₂ rawAssemble := by
  let P := Task × List (List Node)
  have g : Primrec (fun x : P => x.1.1) := Primrec.fst.comp Primrec.fst
  have Δ : Primrec (fun x : P => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have n : Primrec (fun x : P => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have payload := Primrec.nat_div.comp n (Primrec.const 8)
  have pr := Primrec.unpair.comp payload
  have l := Primrec.fst.comp pr
  have r := Primrec.snd.comp pr
  have tag := Primrec.nat_mod.comp n (Primrec.const 8)
  have test (k : Nat) : PrimrecPred (fun x : P => x.1.2.2 % 8 = k) :=
    Primrec.eq.comp tag (Primrec.const k)
  have rs : Primrec (fun x : P => x.2) := Primrec.snd
  have entry (j : Nat) : Primrec (fun x : P => x.2.getD j []) :=
    (Primrec.list_getD []).comp rs (Primrec.const j)
  have dc := Primrec.list_append.comp Δ g
  have dcl := Primrec.list_append.comp (Primrec.list_cons.comp l Δ) g
  have check {u : P → List Nat} {v : P → Nat} (hu : Primrec u) (hv : Primrec v) :
      Primrec (fun x => (SyntaxCode.check (u x) (v x)).getD 0) :=
    Primrec.option_getD.comp (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hu.pair hv)) (Primrec.const 0)
  have τ := check dc n
  have node (k : Nat) {xs : P → List Nat} (hxs : Primrec xs) :
      Primrec (fun x : P => ((x.1.2.1,(SyntaxCode.check (x.1.2.1++x.1.1) x.1.2.2).getD 0,k,xs x) : Node)) :=
    Δ.pair (τ.pair ((Primrec.const k).pair hxs))
  have single {a : P → Node} (h : Primrec a) : Primrec (fun x => [a x]) :=
    Primrec.list_cons.comp h (Primrec.const [])
  have one {a : P → Nat} (h : Primrec a) : Primrec (fun x => [a x]) :=
    Primrec.list_cons.comp h (Primrec.const [])
  have s₀ := single (node 0 (one payload))
  have s₁ := single (node 3 (Primrec.const []))
  have s₂ := single (node 4 (Primrec.const []))
  have s₃ := single (node 5 (one payload))
  have s₄ := single (node 6 (one payload))
  have s₅ := Primrec.list_cons.comp
    (node 1 (Primrec.list_cons.comp (check dc r)
      (Primrec.list_cons.comp (Primrec.list_length.comp (entry 1)) (Primrec.const [0]))))
    (Primrec.list_append.comp (entry 1) (entry 0))
  have s₆ := Primrec.list_cons.comp
    (node 2 (Primrec.list_cons.comp l
      (Primrec.list_cons.comp (check dcl r) (Primrec.const [0]))))
    (entry 0)
  exact Primrec.ite (test 0) s₀ (Primrec.ite (test 1) s₁ (Primrec.ite (test 2) s₂
    (Primrec.ite (test 3) s₃ (Primrec.ite (test 4) s₄ (Primrec.ite (test 5) s₅
      (Primrec.ite (test 6) s₆ (Primrec.const [])))))))

private theorem decreases (a b : Task) (hb : b ∈ rawChildren a) : measure b < measure a := by
  rcases a with ⟨Γ,Δ,n⟩
  unfold rawChildren at hb
  dsimp only at hb
  by_cases h5 : n%8 = 5
  · have hp : 0 < n := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 8)
    simp only [h5,if_true,List.mem_cons,List.mem_singleton] at hb
    rcases hb with e | e
    · subst b
      exact (Nat.unpair_left_le (n/8)).trans_lt hd
    · subst b
      exact (Nat.unpair_right_le (n/8)).trans_lt hd
  · by_cases h6 : n%8 = 6
    · have hp : 0 < n := by omega
      have hd := Nat.div_lt_self hp (by decide : 1 < 8)
      simp only [h5,h6,if_false,if_true,List.mem_singleton] at hb
      subst b
      exact (Nat.unpair_right_le (n/8)).trans_lt hd
    · simp [h5,h6] at hb

private theorem equation (a : Task) :
    rows a.1 a.2.1 a.2.2 =
      rawAssemble a ((rawChildren a).map fun s => rows s.1 s.2.1 s.2.2) := by
  rcases a with ⟨Γ,Δ,n⟩
  change rows Γ Δ n = _
  rw [rows]
  have ht : n%8 = 0 ∨ n%8 = 1 ∨ n%8 = 2 ∨ n%8 = 3 ∨ n%8 = 4 ∨ n%8 = 5 ∨
      n%8 = 6 ∨ n%8 = 7 := by omega
  rcases ht with h | h | h | h | h | h | h | h <;> simp [rawAssemble,rawChildren,h]

private theorem rowsComputable : Computable (fun s : Task => rows s.1 s.2.1 s.2.2) :=
  (LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraph.Proof.exactDecreasingGraph
    Task (List Node) rawChildren rawAssemble measure rawChildrenPrimitive.to_comp rawAssemblePrimitive.to_comp
    (Computable.snd.comp Computable.snd) _ decreases equation).2

theorem rawProgram : CurrentTreeInputCoverageTargets.ActualRawProgram := by
  constructor
  · intro Γ n
    exact Option.map_eq_none_iff
  · have hc := SyntaxCode.StatementChecks.checkPrimitiveRecursive.to_comp
    have hr : Computable (fun x : List Nat × Nat => rows x.1 [] x.2) :=
      rowsComputable.comp (Computable.fst.pair ((Computable.const []).pair Computable.snd))
    have ho : Computable₂ (fun (x : List Nat × Nat) (τ : Nat) => ((x.1,rows x.1 [] x.2,0,τ) : Code)) :=
      ((Computable.fst.comp Computable.fst).pair ((hr.comp Computable.fst).pair
        ((Computable.const 0).pair Computable.snd))).to₂
    exact Computable.option_map hc ho

end LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverage
