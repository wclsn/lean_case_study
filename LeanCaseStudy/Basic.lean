import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

-- 1. Prove a old theorem from new premises
-- 对于一个已经证明的theorem, 用与其前提等价的前提或者其析取前件来替换它
-- have h₂ old := h₂ new

example {a:ℝ} (h₁:a^3>0) : a>0 :=by
  sorry
example {a:ℝ} (h₁:a^2=1) (h₂:a>0): a=1 :=by
  sorry
example {a:ℝ} (h₁:a^2=1) (h₂:a^3>0): a=1 := by
  sorry

---- 另外一个case
example {a b c:ℝ} (h₁: a<b) (h₂: b<c): a<c := by
  apply lt_trans
  . exact h₁
  . exact h₂

example {a b c:ℝ} (h₁: exp a < exp b) (h₂: b < c): a<c:= by
  have h₃: a < b := by apply exp_lt_exp.mp h₁
  apply lt_trans
  . exact h₃
  . exact h₂

-- 同样的，是不是可以用析取的后件来代替要证明的结论，或者与结论等价的结论来替代要证明的结论
-- example case
example {a b c:ℝ} (h₁: a<b) (h₂: b<c): exp a< exp c := by
  have h₃: a < c := by apply lt_trans h₁ h₂
  exact exp_lt_exp.mpr h₃

-- 2. Using existing theorems to get new theorems
-- source_theorem 1
-- source_theorem 2
-- 有一个已经证明的term，可以用可逆的tactic基于其他的前提修改得到新的term，只需要在原来证明的基础上加一些反向操作即可
-- 这个想法有点类似于 conjecture generation, 通过给一个命题手动构造一些断言，然后用已有的证明来生成新的证明
example {a b:ℤ} : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring
example {a b:ℤ} : (a + b) * a = a * a + b * a := by
  rw [add_mul]
example {a b : ℕ} : a * (a + b) + b * (a + b) = a * a + 2 * a * b + b * b:= by
  rw [←add_mul]
  ring

-- neural prover
-- 代数 数论
-- conjecture generation  -> <->  rw  simp
-- theorem mathlib
-- Lean intro  elim
-- () () -> ()
-- () ()-> ()
-- () () () -> ()

--

-- 问题： 除了rewrite还有哪些可逆的tactic可以用来生成新的term
-- 1 和 2 的思想可以统一起来，都是用某些 premise 改写已经证明的 theorem 或者相应的前提条件（具体修改就等价于在当前的证明中引入了新的断言）
-- 可以使用的操作方法 断言引入，可逆tactic

-- 100000
-- 代数
