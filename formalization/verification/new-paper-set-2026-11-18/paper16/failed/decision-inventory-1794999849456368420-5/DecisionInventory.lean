import LogicLineages.PersistentMarking.TypeSupport
namespace LogicLineages.PersistentMarking.DecisionInventory
open Spine NameBridge TypeSupport

/- Finite lists are executable inventories, not quotient sets or cardinality
oracles. Repetitions preserve occurrences and do not affect membership. -/
def declaration (f : Head) : List Ty :=
  subtypes f.result ++ f.arguments.flatMap subtypes

mutual
 def auxiliarySupport : Expr → List Ty
   | .free σ _ | .bound σ _ => subtypes σ
   | .lam σ q => subtypes (.arrow σ q.type) ++ subtypes σ ++ auxiliarySupport q
   | .head f bs => declaration f ++ auxiliaryArgs bs
   | .marked f τ bs es => declaration f ++ subtypes τ ++ auxiliaryArgs bs ++ auxiliaryArgs es
 def auxiliaryArgs : Args → List Ty
   | .nil => []
   | .cons q qs => auxiliarySupport q ++ auxiliaryArgs qs
end
mutual
 def freeInventory : Expr → List Name
   | .free σ x => [(σ,x)]
   | .bound _ _ => []
   | .lam _ q => freeInventory q
   | .head _ bs => freeInventoryArgs bs
   | .marked _ _ bs es => freeInventoryArgs bs ++ freeInventoryArgs es
 def freeInventoryArgs : Args → List Name
   | .nil => []
   | .cons q qs => freeInventory q ++ freeInventoryArgs qs
end
mutual
 def heads : Expr → List Head
   | .free _ _ | .bound _ _ => []
   | .lam _ q => heads q
   | .head f bs => f :: headsArgs bs
   | .marked f _ bs es => f :: (headsArgs bs ++ headsArgs es)
 def headsArgs : Args → List Head
   | .nil => []
   | .cons q qs => heads q ++ headsArgs qs
end
mutual
 def lambdaDepth : Expr → Nat
   | .free _ _ | .bound _ _ => 0
   | .lam _ q => 1 + lambdaDepth q
   | .head _ bs => lambdaDepthArgs bs
   | .marked _ _ bs es => max (lambdaDepthArgs bs) (lambdaDepthArgs es)
 def lambdaDepthArgs : Args → Nat
   | .nil => 0
   | .cons q qs => max (lambdaDepth q) (lambdaDepthArgs qs)
end

/- Counts lambdas on actual syntax paths, including base and extra paths. -/
mutual
 inductive LambdaPath : Expr → Nat → Prop where
   | root : LambdaPath q 0
   | lam : LambdaPath q n → LambdaPath (.lam σ q) (n+1)
   | head : LambdaPathArgs bs n → LambdaPath (.head f bs) n
   | markedBase : LambdaPathArgs bs n → LambdaPath (.marked f τ bs es) n
   | markedExtra : LambdaPathArgs es n → LambdaPath (.marked f τ bs es) n
 inductive LambdaPathArgs : Args → Nat → Prop where
   | here : LambdaPath q n → LambdaPathArgs (.cons q qs) n
   | there : LambdaPathArgs qs n → LambdaPathArgs (.cons q qs) n
end

structure InputInventory where
  types : List Ty
  names : List Name
  sourceHeads : List Head
  ports : Nat

def inventory (s t : Expr) : InputInventory :=
  ⟨support s ++ support t, freeInventory s ++ freeInventory t, heads s, lambdaDepth t⟩
end LogicLineages.PersistentMarking.DecisionInventory
