import Mathlib
import Smt

-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Real.Sqrt

open Real

@[inherit_doc] prefix:max "sqrt" => Real.sqrt

example {a b c : ℝ} : 0 ≥ a := by
  smt_decide

example {a b c : Real} (h : b ≥ 0) : 0 ≤ sqrt b := by
  smt_decide! (solver := cvc5)

example {a b c : ℝ} : 0 ≤ a ^ 2 := by
  smt_decide

example {a b c : Real} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  smt_decide

example {a b c : Real} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  smt_decide! (solver := cvc5)

example {a b c : Real} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  sos!

theorem P1 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b + b * c + c * d + d * a = 1) : 1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by
  smt_decide! (solver := cvc5)
