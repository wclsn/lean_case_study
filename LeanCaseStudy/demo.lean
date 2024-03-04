import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real
/-
  This file contains the basic demo which shows how to synthesize the data.

  e.g. repl the premise and proof statement
       and then insert a conjecture
 -/

theorem orig_iff_1 {a:ℝ} (h₁:a^3>0) : a>0 :=by
  sorry

theorem orig_iff_2 {a:ℝ} (h₁:a^2=1) (h₂:a>0): a=1 :=by
  sorry

theorem iff_res {a:ℝ} (h₁:a^2=1) (h₂:a^3>0): a=1 := by
  sorry

theorem orig_iff__1 {a b c:ℝ} (h₁: a<b) (h₂: b<c): a<c := by
  apply lt_trans
  . exact h₁
  . exact h₂

theorem res_iff_1 {a b c:ℝ} (h₁: exp a < exp b) (h₂: b < c): a<c:= by
  have h₃: a < b := by apply exp_lt_exp.mp h₁
  apply lt_trans
  . exact h₃
  . exact h₂

theorem res_iff_2 {a b c:ℝ} (h₁: a<b) (h₂: b<c): exp a< exp c := by
  have h₃: a < c := by apply lt_trans h₁ h₂
  exact exp_lt_exp.mpr h₃

theorem orig_rw_1 {a b:ℤ} : (a + b) * a = a * a + b * a := by
  rw [add_mul]

theorem orig_rw_2 {a b:ℤ} : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  ring

theorem res_after_rw {a b : ℕ} : a * (a + b) + b * (a + b) = a * a + 2 * a * b + b * b:= by
  rw [←add_mul]
  ring
